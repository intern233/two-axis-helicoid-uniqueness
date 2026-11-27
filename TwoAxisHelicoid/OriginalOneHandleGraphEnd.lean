import TwoAxisHelicoid.HelicoidEndReparameterization
import TwoAxisHelicoid.AmbientHarmonicImmersion
import TwoAxisHelicoid.ArbitraryHelicoidalEndPoles
import TwoAxisHelicoid.MarkedHolomorphicFilling
import TwoAxisHelicoid.PhysicalGraphPunctureFilling
import TwoAxisHelicoid.OpenSubdomainLocalBiholomorphism
import TwoAxisHelicoid.HalfPlaneGaussMorseIndex
import TwoAxisHelicoid.ClassicalRiemannUniformizationSpecialization

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- The geometric two-pole end in the original isothermal atlas of a
one-handled surface with a single physical helicoidal normal graph.
Only simply connected uniformization is an external input. -/
theorem original_one_handle_graph_double_pole_end {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) (uni : SimplyConnectedNoncompactUniformization.{u})
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    Nonempty (GeometricDoublePoleEnd X) := by
  let := punctured_complex_curve_noncompact (0:PeriodTorus L₀)
  have non : NoncompactSpace M := ⟨fun h => noncompact_univ (PuncturedPeriodTorus L₀) (by
    simpa only [image_univ,top.surjective.range_eq] using h.image top.continuous)⟩
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling closed charts graph (topological_plane_uniformization_of_classical uni)
  obtain ⟨L,f,Y,hf,hi,pos,cl,_,regular⟩ := marked_harmonic_torus_of_filling top (compact_genus_one_uniformization_of_classical uni _)
    X closed charts E hol
  let Yp := fun q : PuncturedPeriodTorus L => Y q.1
  let Z := puncturedTorusPullback L Yp
  have offeq (z : ℂ) (hz : z∉L.lattice) : Z=ᶠ[𝓝 z] Y ∘ periodTorusProjection L := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    change w∉L.lattice at hw
    simp [Z,Yp,puncturedTorusPullback,hw,puncturedPlaneProjection]
  have reg (z : ℂ) (hz : z∉L.lattice) : (∀ j, HarmonicAt (fun w => Z w j) z) ∧
      ConformalCoordinateDerivatives Z z ∧ Function.Injective (fderiv ℝ Z z) := by
    have e := offeq z hz
    obtain ⟨h,c,i⟩ := regular z hz
    have dy : DifferentiableAt ℝ (Y ∘ periodTorusProjection L) z := (spatial_harmonic_of_coordinates h).1.differentiableAt two_ne_zero
    refine ⟨fun j => (harmonicAt_congr_nhds (e.mono fun w h => congrFun h j)).mpr (h j),?_,by rwa [e.fderiv_eq]⟩
    apply (conformalCoordinateDerivatives_iff_dot (dy.congr_of_eventuallyEq e)).mpr
    rw [e.fderiv_eq]
    exact (conformalCoordinateDerivatives_iff_dot dy).mp c
  have eq : (coordinateToTube ∘ X) ∘ f.symm=coordinateToTube ∘ Yp := by
    funext q
    exact congrArg coordinateToTube ((pos (f.symm q)).symm.trans (congrArg (fun a => Y a.1) (f.apply_symm_apply q)))
  obtain ⟨⟨hm,ho⟩,gm,go⟩ := arbitrary_helicoidal_torus_two_double_poles L Yp cl.isProperMap (eq ▸ graph.comp_homeomorph f.symm) reg
  have near : Z=ᶠ[𝓝[≠] (0:ℂ)] Y ∘ periodTorusProjection L :=
    (punctured_lattice_regular_near_zero L).mono fun z hz => (offeq z hz).eq_of_nhds
  obtain ⟨forms,logs⟩ := spatial_equal_germ_end_coefficients near
  let := periodTorus_compactSpace L
  obtain ⟨e,es,proj⟩ := periodTorusProjection_isLocalHomeomorph L (0:ℂ)
  have zero : e 0=0 := (congrFun proj 0).symm.trans ((periodTorusProjection_eq_zero L 0).mpr L.lattice.zero_mem)
  have localChart : e.symm∈atlas ℂ (PeriodTorus L) := proj.symm
  let D : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M (PuncturedPeriodTorus L) ω := ⟨f.toEquiv,hf,hi⟩
  have loc : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x => (f x).1) := fun x =>
    IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ,ℂ)) (P := PeriodTorus L) (D.isLocalDiffeomorph x)
      (open_complex_subdomain_local_biholomorphism (puncturedPeriodTorusOpen L) (f x))
  obtain ⟨a,ha⟩ := (marked_torus_lattice_complement_connected L).nonempty
  let b := f.symm (puncturedPlaneProjection L ⟨a,ha⟩)
  apply abstract_conformal_filling_gives_double_pole_end b (0:PeriodTorus L) f loc e.symm
    (IsManifold.subset_maximalAtlas localChart) (zero ▸ e.map_source es) (zero ▸ e.left_inv es) X Y pos
  all_goals rw [show (e.symm.symm : ℂ → PeriodTorus L)=periodTorusProjection L from proj.symm]
  · exact hm.congr (forms.fun_comp (fun p => p 2))
  · exact ((meromorphicOrderAt_congr (forms.mono fun z h => congrFun h 2)).symm.trans ho).trans (by norm_num)
  · exact gm.congr logs
  · exact ((meromorphicOrderAt_congr logs).symm.trans go).trans (by norm_num)

/-- Infinite compactly supported Morse index in the actual smooth
one-handled surface, without any symmetry or straight axis. -/
theorem original_one_handle_graph_infinite_morse_index {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L₀) (uni : SimplyConnectedNoncompactUniformization.{u})
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    HasInfiniteCompactSurfaceMorseIndex X := by
  obtain ⟨A⟩ := original_one_handle_graph_double_pole_end top uni X closed charts graph
  exact geometric_double_pole_end_infinite_morse_index charts A

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_one_handle_graph_double_pole_end
#print axioms TwoAxisHelicoid.original_one_handle_graph_infinite_morse_index
