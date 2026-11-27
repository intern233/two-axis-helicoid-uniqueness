import TwoAxisHelicoid.WeierstrassCoordinateData
import TwoAxisHelicoid.HolomorphicNullImmersion

namespace TwoAxisHelicoid
open Complex Set Metric InnerProductSpace

/-- For the actual manuscript data, every point off the puncture has a real
analytic conformal harmonic immersion obtained by integrating the coordinate
forms. This includes the finite zeros/poles of the displayed Gauss quotient. -/
theorem actual_coordinate_local_immersion {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 1) (hc : c ≠ 0) {z₀ : ℂ}
    (hz₀ : z₀ ∉ (rhombicPeriodPair t ht).lattice) :
    ∃ r : ℝ, 0 < r ∧ ball z₀ r ⊆ ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ ∧
      ∃ X : ℂ → Fin 3 → ℝ,
      X z₀ = 0 ∧ AnalyticOnNhd ℝ X (ball z₀ r) ∧ HarmonicOnNhd X (ball z₀ r) ∧
      ∀ z ∈ ball z₀ r,
        fderiv ℝ X z = nullRealDerivative (coordinateData t a c ht z) ∧
        Function.Injective (fderiv ℝ X z) ∧
        0 < nullMetric (coordinateData t a c ht z) ∧
        (∑ j, (fderiv ℝ X z 1 j)^2) = nullMetric (coordinateData t a c ht z) ∧
        (∑ j, (fderiv ℝ X z I j)^2) = nullMetric (coordinateData t a c ht z) ∧
        (∑ j, fderiv ℝ X z 1 j*fderiv ℝ X z I j) = 0 := by
  apply holomorphic_null_local_immersion
    (rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl
    (fun _ hz => coordinateData_analyticAt ht hz)
    (fun _ hz => coordinateData_null ht ha hz)
    (fun _ hz => coordinateData_ne_zero ht ha hc hz) hz₀

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_coordinate_local_immersion
