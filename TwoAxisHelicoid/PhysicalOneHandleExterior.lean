import TwoAxisHelicoid.TorusWindingHeightChart
import TwoAxisHelicoid.PhysicalGraphWindingElimination
import TwoAxisHelicoid.OriginalOneHandleGraphEnd
import TwoAxisHelicoid.GeometricExteriorPullback

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- The exponential exterior normal form of the physical one-handled
helicoid in its own unit-pitch frame. No straight line or global
embeddedness of the marked harmonic core is used. -/
theorem arbitrary_torus_physical_exterior (L : PeriodPair) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ)
    (proper : IsProperMap Y) (graph : HasHelicoidC1End (coordinateToTube ∘ Y))
    (reg : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z)) :
    Nonempty (GeometricExteriorCoordinate Y) := by
  obtain ⟨e,R,m,c,B,rp,target,core,hol,height,cn,ba,bn,measured⟩ := arbitrary_torus_winding_height_chart L Y proper graph reg
  obtain ⟨rfl,rfl⟩ := physical_graph_winding_elimination graph proper.continuous e target height m cn ba.continuousAt bn
    (measured.mono fun _ h => h.2)
  let f := fun z => log (B z/B 0)+log (B 0)
  have slit : B 0/B 0∈slitPlane := by rw [div_self bn]; exact one_mem_slitPlane
  have fa : AnalyticAt ℂ f 0 := ((ba.div_const).clog slit).add analyticAt_const
  have val : ∀ᶠ z in 𝓝 (0:ℂ), exp (f z)=B z := by
    filter_upwards [ba.continuousAt.eventually_ne bn] with z h
    dsimp [f]
    rw [exp_add,exp_log (div_ne_zero h bn),exp_log bn,div_mul_cancel₀ _ bn]
  refine ⟨⟨e,R,rp,target,core,hol,0,fun x hx => (height x hx).trans (zero_add _).symm,1,one_ne_zero,f,fa,?_⟩⟩
  filter_upwards [measured,tendsto_inv₀_cobounded.eventually val] with w h fact
  rw [h.1,zpow_zero,one_mul,ofReal_one,mul_one,exp_add,fact]

/-- A one-ended embedded minimal surface of torus topology with a
physical unit-pitch normal graph carries its own analytic exterior
coordinate. The sole outside assumption is classical simply connected
uniformization. -/
theorem original_one_handle_physical_exterior {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uni : SimplyConnectedNoncompactUniformization.{u}) (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    Nonempty (GeometricExteriorCoordinate X) := by
  let := punctured_complex_curve_noncompact (0:PeriodTorus L₀)
  have non : NoncompactSpace M := ⟨fun h => noncompact_univ (PuncturedPeriodTorus L₀) (by
    simpa only [image_univ,top.surjective.range_eq] using h.image top.continuous)⟩
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling closed charts graph (topological_plane_uniformization_of_classical uni)
  obtain ⟨L,f,Y,hf,hi,pos,cl,_,regular⟩ := marked_harmonic_torus_of_filling top (compact_genus_one_uniformization_of_classical uni _) X closed charts E hol
  let Yp := fun q : PuncturedPeriodTorus L => Y q.1
  let Z := puncturedTorusPullback L Yp
  have reg (z : ℂ) (hz : z∉L.lattice) : (∀ j, HarmonicAt (fun w => Z w j) z) ∧
      ConformalCoordinateDerivatives Z z ∧ Function.Injective (fderiv ℝ Z z) := by
    have e : Z=ᶠ[𝓝 z] Y ∘ periodTorusProjection L := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      change w∉L.lattice at hw
      simp [Z,Yp,puncturedTorusPullback,hw,puncturedPlaneProjection]
    obtain ⟨h,c,i⟩ := regular z hz
    have dy : DifferentiableAt ℝ (Y ∘ periodTorusProjection L) z := (spatial_harmonic_of_coordinates h).1.differentiableAt two_ne_zero
    refine ⟨fun j => (harmonicAt_congr_nhds (e.mono fun w h => congrFun h j)).mpr (h j),?_,by rwa [e.fderiv_eq]⟩
    apply (conformalCoordinateDerivatives_iff_dot (dy.congr_of_eventuallyEq e)).mpr
    rw [e.fderiv_eq]
    exact (conformalCoordinateDerivatives_iff_dot dy).mp c
  have eq : (coordinateToTube ∘ X) ∘ f.symm=coordinateToTube ∘ Yp := by
    funext q
    exact congrArg coordinateToTube ((pos (f.symm q)).symm.trans (congrArg (fun a => Y a.1) (f.apply_symm_apply q)))
  obtain ⟨A⟩ := arbitrary_torus_physical_exterior L Yp cl.isProperMap (eq ▸ graph.comp_homeomorph f.symm) reg
  exact geometric_exterior_coordinate_pullback f hf hi pos A

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.arbitrary_torus_physical_exterior
#print axioms TwoAxisHelicoid.original_one_handle_physical_exterior
