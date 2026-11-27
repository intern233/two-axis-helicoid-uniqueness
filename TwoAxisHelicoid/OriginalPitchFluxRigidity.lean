import TwoAxisHelicoid.OriginalGraphExteriorNormalization
import TwoAxisHelicoid.OriginalExteriorGaussRigidity

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- For a graph end of any nonzero signed pitch, both rigidity
statements of Appendix C, the first-order multiplier test and an actual
nonvertical conormal integral hold in a common marking. The original
position map is used in its given spatial frame. -/
theorem original_finite_pitch_flux_and_fixed_data {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uni : SimplyConnectedNoncompactUniformization.{u}) (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
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
  obtain ⟨A,_⟩ := one_handle_original_frame_exterior top uni X closed hX ha graph
  obtain ⟨L,f,Y,hf,hi,eq,endData,flux,loop⟩ := original_exterior_one_handle_has_horizontal_flux top
    (compact_genus_one_uniformization_of_classical uni _) X closed hX A
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
#print axioms TwoAxisHelicoid.original_finite_pitch_flux_and_fixed_data
