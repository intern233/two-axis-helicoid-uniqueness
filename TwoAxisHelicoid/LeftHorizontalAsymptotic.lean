import TwoAxisHelicoid.LeftNormalizedChordLimit
import TwoAxisHelicoid.LeftPeriodError
import TwoAxisHelicoid.OriginalPeriodBridge
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace TwoAxisHelicoid
open Set Filter MeasureTheory Asymptotics
open scoped Topology
set_option maxHeartbeats 1200000
attribute [local irreducible] verticalA actualPeriodAlong leftComparisonPeriod

noncomputable def leftHorizontalMainTerm (t : ℝ) : ℝ :=
  (t/Real.pi)*Real.exp (Real.pi/(2*t))

theorem leftHorizontalMainTerm_pos {t : ℝ} (ht : 0 < t) : 0 < leftHorizontalMainTerm t := by
  unfold leftHorizontalMainTerm
  positivity

theorem leftComparisonPeriod_div_main_eq {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftComparisonPeriod t/leftHorizontalMainTerm t =
      (leftKappa0 t/leftKappa t)^2*Real.exp (-leftEpsilon t)*leftNormalizedChordIntegral t := by
  have hκ : 0 < leftKappa t := by linarith [leftKappa_gt ht htu]
  have he : Real.exp (-leftEpsilon t) = Real.exp (-leftKappa0 t)*Real.exp (leftKappa t) := by
    rw [← Real.exp_add,leftKappa_eq_kappa0_sub_epsilon]
    congr 1
    ring
  rw [leftComparisonPeriod_eq_chord ht,he,leftNormalizedChordIntegral,leftHorizontalMainTerm,leftKappa0]
  simp only [Real.exp_neg]
  field_simp [ht.ne',hκ.ne',Real.pi_ne_zero,Real.exp_ne_zero (Real.pi/(2*t)),Real.exp_ne_zero (leftKappa t)]

theorem leftComparisonPeriod_div_main_tendsto_one :
    Tendsto (fun t : ℝ => leftComparisonPeriod t/leftHorizontalMainTerm t)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hr : Tendsto (fun t : ℝ => leftKappa0 t/leftKappa t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [inv_div,inv_one] using leftKappa_div_kappa0_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have he : Tendsto (fun t : ℝ => Real.exp (-leftEpsilon t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def,neg_zero,Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp leftEpsilon_tendsto_zero.neg
  have h := ((hr.pow 2).mul he).mul leftNormalizedChordIntegral_tendsto_one
  simp only [one_pow,mul_one] at h
  apply h.congr'
  filter_upwards [eighth_height_eventually_right] with t ht
  exact (leftComparisonPeriod_div_main_eq ht.1 ht.2).symm

theorem actualPeriodAlong_comparison_scaled_error {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    |(actualPeriodAlong t-leftComparisonPeriod t)/leftHorizontalMainTerm t| ≤
      276*(leftKappa0 t)^2*Real.exp (-leftKappa0 t) := by
  have hpos := leftHorizontalMainTerm_pos ht
  rw [abs_div,abs_of_pos hpos]
  have hb := div_le_div_of_nonneg_right (leftPeriod_error_lt ht htu).le hpos.le
  refine hb.trans_eq ?_
  unfold leftHorizontalMainTerm leftKappa0
  rw [Real.exp_neg]
  field_simp [ht.ne',Real.pi_ne_zero,Real.exp_ne_zero (Real.pi/(2*t))]
  ring

theorem actualPeriodAlong_comparison_scaled_error_tendsto_zero :
    Tendsto (fun t : ℝ => (actualPeriodAlong t-leftComparisonPeriod t)/leftHorizontalMainTerm t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall (fun _ => abs_nonneg _)
  · filter_upwards [eighth_height_eventually_right] with t ht
    exact actualPeriodAlong_comparison_scaled_error ht.1 ht.2
  · simpa only [Function.comp_def,mul_zero,mul_assoc] using
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp leftKappa0_tendsto_atTop).const_mul 276

/-- The actual horizontal period has exactly the left-end main term stated in
Appendix B.1. The comparison error is removed using the already proved uniform
full-path product estimate. -/
theorem actualPeriodAlong_div_left_main_tendsto_one :
    Tendsto (fun t : ℝ => actualPeriodAlong t/((t/Real.pi)*Real.exp (Real.pi/(2*t))))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := actualPeriodAlong_comparison_scaled_error_tendsto_zero.add
    leftComparisonPeriod_div_main_tendsto_one
  simp only [zero_add] at h
  apply h.congr
  intro t
  unfold leftHorizontalMainTerm
  ring

theorem actualPeriodAlong_left_asymptotic :
    actualPeriodAlong ~[𝓝[>] (0 : ℝ)] (fun t : ℝ => (t/Real.pi)*Real.exp (Real.pi/(2*t))) := by
  apply isEquivalent_of_tendsto_one
  change Tendsto (fun t : ℝ => actualPeriodAlong t/((t/Real.pi)*Real.exp (Real.pi/(2*t))))
    (𝓝[>] (0 : ℝ)) (𝓝 1)
  exact actualPeriodAlong_div_left_main_tendsto_one

/-- The original sigma/sloping-path definition of the manuscript's period has
the same asymptotic, by its proved identity with the actual theta period. -/
theorem originalPeriodAlong_left_asymptotic :
    originalPeriodAlong ~[𝓝[>] (0 : ℝ)] (fun t : ℝ => (t/Real.pi)*Real.exp (Real.pi/(2*t))) := by
  apply isEquivalent_of_tendsto_one
  have h := actualPeriodAlong_div_left_main_tendsto_one
  apply h.congr'
  filter_upwards [small_height_eventually_right] with t ht
  change actualPeriodAlong t/((t/Real.pi)*Real.exp (Real.pi/(2*t))) =
    originalPeriodAlong t/((t/Real.pi)*Real.exp (Real.pi/(2*t)))
  rw [originalPeriodAlong_eq_actual (small_height_mem_vertical_domain ht.1 ht.2)]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_left_asymptotic
#print axioms TwoAxisHelicoid.originalPeriodAlong_left_asymptotic
