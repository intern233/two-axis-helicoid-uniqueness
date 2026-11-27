import TwoAxisHelicoid.ProvedPlaneUniformization
import TwoAxisHelicoid.GenusOneFromAnnularUniformization
import TwoAxisHelicoid.OriginalPitchFluxRigidity

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- The actual exterior coordinate for a properly embedded one-handle
physical graph follows from the proven plane and torus uniformizations. -/
theorem one_handle_physical_exterior_proved {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    Nonempty (GeometricExteriorCoordinate X) := by
  let := punctured_complex_curve_noncompact (0:PeriodTorus L₀)
  have non : NoncompactSpace M := ⟨fun h => noncompact_univ (PuncturedPeriodTorus L₀) (by
    simpa only [image_univ,top.surjective.range_eq] using h.image top.continuous)⟩
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling closed charts graph topological_plane_uniformization_proved
  obtain ⟨L,f,Y,hf,hi,pos,cl,_,regular⟩ := marked_harmonic_torus_of_filling top (compact_genus_one_uniformization_of_annular_classification annular_riemann_surface_uniformization_proved _) X closed charts E hol
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

/-- Transport the constructed coordinate back to arbitrary nonzero
signed pitch and normalize its additive and phase constants. -/
theorem finite_pitch_exterior_in_original_frame {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e) {α : ℝ} (a : α≠0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization a ![0,0,0] ∘ X)) :
    ∃ A : GeometricExteriorCoordinate X, A.correction 0=0 := by
  let R := axisSpatialNormalization a ![0,0,0]
  let Y := R ∘ X
  have cy : ∀ e∈atlas ℂ M, HarmonicImmersionChart Y e :=
    fun e he z hz => reference_frame_harmonic_chart (charts e he z hz).1 (charts e he z hz).2.1 (charts e he z hz).2.2 a
  obtain ⟨A⟩ := one_handle_physical_exterior_proved top Y (R.isClosedEmbedding.comp closed) cy graph
  exact physical_exterior_back_in_original_frame top X closed charts a A


/-- The horizontal flux loop and the two rigidity statements of
Appendix C hold in one common marking of the original surface,
for every C¹ helicoidal graph end, with no axis symmetry required. -/
theorem appendix_C_nonvertical_flux_and_rigidity {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (hX : ∀ e ∈ atlas ℂ M, HarmonicImmersionChart X e) {α : ℝ} (ha : α≠0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ X)) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧ (∀ p, Y (f p)=X p) ∧
      MarkedHelicoidalEndForms L Y ∧ HasIntrinsicNonverticalFlux L Y ∧
      (∃ (p : M) (γ : Path p p) (q : PuncturedPeriodTorus L) (δ : Path q q) (j : Fin 3) (v : ℝ),
        (∀ t, f (γ t)=δ t) ∧ (∀ t, Y (δ t)=X (γ t)) ∧ j≠2 ∧ v≠0 ∧ TorusSpatialConormalIntegral L Y j δ v) ∧
      (∀ {k : ℝ → ℂ} {d : ℂ}, HasDerivAt k d 0 → k 0=1 → (LopezRosClosedToFirstOrder L Y k ↔ d.re=0)) ∧
      ∀ Z : PuncturedPeriodTorus L → Fin 3 → ℝ,
      (∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Z w j) z) ∧ ConformalCoordinateDerivatives (puncturedTorusPullback L Z) z) →
      (((∀ z ∉ L.lattice, torusImmersionForms L Z z 2=torusImmersionForms L Y z 2) ∧
        (∀ z ∉ L.lattice, torusImmersionForms L Y z 2 ≠ 0 →
          immersionGaussLog (torusImmersionForms L Z) z=immersionGaussLog (torusImmersionForms L Y) z)) ∨
       (CommonLaurentPartAt (fun z => torusImmersionForms L Y z 2) (fun z => torusImmersionForms L Z z 2) 0 ∧
        ∀ z, CommonLaurentPartAt (immersionGaussLog (torusImmersionForms L Y)) (immersionGaussLog (torusImmersionForms L Z)) z)) →
      ∃ (θ : ℝ) (b : Fin 3 → ℝ), (∀ p : M, Z (f p)=verticalRotation (exp ((θ:ℂ)*I)) (X p)+b) ∧
        ∀ q, torusSphericalGauss L Z q=OnePoint.map (exp ((θ:ℂ)*I)*·) (torusSphericalGauss L Y q) := by
  obtain ⟨A,_⟩ := finite_pitch_exterior_in_original_frame top X closed hX ha graph
  obtain ⟨L,f,Y,hf,hi,eq,endData,flux,loop⟩ := original_exterior_one_handle_has_horizontal_flux top
    (compact_genus_one_uniformization_of_annular_classification annular_riemann_surface_uniformization_proved _) X closed hX A
  have hY (z : ℂ) (h : z ∉ L.lattice) := And.intro (endData.regular z h).1 (endData.regular z h).2.1
  refine ⟨L,f,Y,hf,hi,eq,endData,flux,loop,fun hk hk0 => lopez_ros_first_order_closure_iff_rotation L Y hY flux hk hk0,?_⟩
  intro Z hZ h
  have motion : ∃ (θ : ℝ) (b : Fin 3 → ℝ), ∀ q, Z q=verticalRotation (exp ((θ:ℂ)*I)) (Y q)+b := by
    rcases h with ⟨hh,hg⟩ | ⟨hh,hg⟩
    · exact intrinsic_punctured_torus_fixed_log_rigidity L Y Z hY hZ endData.height_order hh hg flux
    · exact intrinsic_punctured_torus_fixed_parts_rigidity L Y Z hY hZ endData.height_order hh hg flux
  obtain ⟨θ,b,he⟩ := motion
  exact ⟨θ,b,fun p => (eq p) ▸ he (f p),torusSphericalGauss_rotate L Y Z hY hZ (by simp [Complex.norm_exp]) he⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.appendix_C_nonvertical_flux_and_rigidity
