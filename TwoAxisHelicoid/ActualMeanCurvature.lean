import TwoAxisHelicoid.CoordinateMeanCurvature
import TwoAxisHelicoid.ActualGlobalImmersion

namespace TwoAxisHelicoid
open Complex Matrix Set

/-- The actual closed coordinate primitive has a genuine unit normal and
zero standard mean curvature at every regular parameter point. -/
theorem actual_global_primitive_mean_curvature_zero {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    coordinateMeanCurvature (actualGlobalImmersion t a c ht) z = 0 ∧
      let N := unitCrossNormal (fderiv ℝ (actualGlobalImmersion t a c ht) z 1)
        (fderiv ℝ (actualGlobalImmersion t a c ht) z I)
      N ⬝ᵥ N = 1 ∧ N ⬝ᵥ fderiv ℝ (actualGlobalImmersion t a c ht) z 1 = 0 ∧
        N ⬝ᵥ fderiv ℝ (actualGlobalImmersion t a c ht) z I = 0 := by
  have h := actual_global_conformal_harmonic_immersion ht ha hc hG hH
  have hg := (h.2.2.2 z hz).2.2
  have hA : fderiv ℝ (actualGlobalImmersion t a c ht) z 1 ⬝ᵥ
      fderiv ℝ (actualGlobalImmersion t a c ht) z 1 = nullMetric (coordinateData t a c ht z) := by
    simpa only [dotProduct,pow_two] using hg.2.1
  have hB : fderiv ℝ (actualGlobalImmersion t a c ht) z I ⬝ᵥ
      fderiv ℝ (actualGlobalImmersion t a c ht) z I = nullMetric (coordinateData t a c ht z) := by
    simpa only [dotProduct,pow_two] using hg.2.2.1
  have hAB : fderiv ℝ (actualGlobalImmersion t a c ht) z 1 ⬝ᵥ
      fderiv ℝ (actualGlobalImmersion t a c ht) z I = 0 := hg.2.2.2
  exact ⟨conformal_harmonic_coordinate_mean_curvature_zero (h.2.2.1 z hz) hA hB hAB,
    conformal_unitCrossNormal hg.1 hA hB hAB⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_global_primitive_mean_curvature_zero
