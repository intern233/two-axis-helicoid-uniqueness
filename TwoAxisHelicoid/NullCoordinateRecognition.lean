import TwoAxisHelicoid.NullGaussDivisor
import TwoAxisHelicoid.WeierstrassSimilarity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem null_eq_weierstrassTriple {p : Fin 3 → ℂ} (hp : ComplexNull p) (hh : p 2 ≠ 0) :
    p = weierstrassTriple (nullGauss p) (p 2) := by
  have h := null_gauss_reconstruct hp hh
  ext j
  fin_cases j
  · change p 0 = ((nullGauss p)⁻¹-nullGauss p)/2*p 2
    rw [← h.1,one_div]
    ring
  · change p 1 = I*((nullGauss p)⁻¹+nullGauss p)/2*p 2
    rw [← h.2,one_div]
    ring
  · rfl

/-- Identifies actual analytic null coefficients with the globally regular
coordinate formula, including both finite zeros of the height differential.
Only the Gauss formula away from its zero/pole representatives is needed. -/
theorem null_coefficients_eq_phased_coordinateData {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) {q : ℂ} (hq : ‖q‖ = 1)
    {p : ℂ → Fin 3 → ℂ}
    (hp : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ComplexNull (p z))
    (hA : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = I*c*((rhombicPeriodPair t ht).weierstrassP z-
        (rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (p z) = q*thetaGauss t a 1 z) :
    ∀ z ∉ (rhombicPeriodPair t ht).lattice, p z = phasedCoordinateData t a c ht q z := by
  have hregular (z : ℂ) (hz : z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a) :
      p z = phasedCoordinateData t a c ht q z := by
    have h := (not_mem_gaussLogPoleSet (rhombicPeriodPair t ht) a z).mp hz
    have hh0 := null_height_nonzero_away_pair ht ha
      (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)) hh hz
    rw [null_eq_weierstrassTriple (hp z h.1) hh0,hg z hz,hh z h.1]
    exact (phasedCoordinateData_eq_original ht ha hq h.1 h.2.1 h.2.2).symm
  intro z hz
  have hpc : ContinuousAt p z := continuousAt_pi.mpr (fun j => (hA z hz j).continuousAt)
  have hdc := (coordinateData_analyticAt (a := a) (c := c) ht hz).continuousAt
  have hqc : ContinuousAt (phasedCoordinateData t a c ht q) z := by
    apply continuousAt_pi.mpr
    intro j
    fin_cases j
    · exact (continuousAt_const.mul (continuousAt_pi.mp hdc 0)).sub
        (continuousAt_const.mul (continuousAt_pi.mp hdc 1))
    · exact (continuousAt_const.mul (continuousAt_pi.mp hdc 0)).add
        (continuousAt_const.mul (continuousAt_pi.mp hdc 1))
    · exact continuousAt_pi.mp hdc 2
  have he : p =ᶠ[𝓝[≠] z] phasedCoordinateData t a c ht q := by
    filter_upwards [latticePoleSet_punctured_avoids (rhombicPeriodPair t ht)
      (show ({0,(a : ℂ),-(a : ℂ)} : Set ℂ).Finite by simp) z] with w hw
    exact hregular w hw
  exact tendsto_nhds_unique (hpc.tendsto.mono_left nhdsWithin_le_nhds)
    ((hqc.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.null_coefficients_eq_phased_coordinateData
