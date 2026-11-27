import TwoAxisHelicoid.PhysicalOneHandleExterior
import TwoAxisHelicoid.OriginalExteriorGaussRigidity

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

universe u

/-- On the original physical normal graph, a closed curve carries
nonzero horizontal conormal flux. The analytic exterior and the
nonvertical flux are both conclusions and neither straight axis is
assumed. -/
theorem physical_one_handle_has_horizontal_flux {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uni : SimplyConnectedNoncompactUniformization.{u}) (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d) (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧
      (∀ p, Y (f p)=X p) ∧ MarkedHelicoidalEndForms L Y ∧ HasIntrinsicNonverticalFlux L Y ∧
      ∃ (p : M) (γ : Path p p) (q : PuncturedPeriodTorus L) (δ : Path q q) (j : Fin 3) (v : ℝ),
      (∀ t, f (γ t)=δ t) ∧ (∀ t, Y (δ t)=X (γ t)) ∧ j ≠ 2 ∧ v ≠ 0 ∧ TorusSpatialConormalIntegral L Y j δ v := by
  obtain ⟨A⟩ := original_one_handle_physical_exterior top uni X closed hX graph
  exact original_exterior_one_handle_has_horizontal_flux top (compact_genus_one_uniformization_of_classical uni _) X closed hX A

/-- Appendix C.4 and C.5 for a fixed marked original graph, including
the exact first-order condition on a Lopez--Ros multiplier. -/
theorem physical_one_handle_fixed_data_rigidity {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uni : SimplyConnectedNoncompactUniformization.{u}) (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (hX : ∀ e ∈ atlas ℂ M, HarmonicImmersionChart X e) (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    ∃ (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PuncturedPeriodTorus L → Fin 3 → ℝ),
      ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f ∧ ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm ∧ (∀ p, Y (f p)=X p) ∧
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
  obtain ⟨A⟩ := original_one_handle_physical_exterior top uni X closed hX graph
  exact original_exterior_fixed_data_rigidity top (compact_genus_one_uniformization_of_classical uni _) X closed hX A

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_one_handle_has_horizontal_flux
#print axioms TwoAxisHelicoid.physical_one_handle_fixed_data_rigidity
