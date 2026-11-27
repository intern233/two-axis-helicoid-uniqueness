import TwoAxisHelicoid.LeftComparisonChord
import TwoAxisHelicoid.LeftChordIntegralLower

namespace TwoAxisHelicoid
open Set
set_option maxHeartbeats 800000
attribute [local irreducible] verticalA

theorem actual_left_chord_parameters {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    0 < leftChordH (leftNome t) ∧ 0 ≤ leftChordK (leftNome t) ∧
      (leftChordH (leftNome t))^2+(leftChordK (leftNome t))^2 = 1 ∧
      leftKappa t*leftChordH (leftNome t) ≤ 1/10 := by
  have hq0 := leftNome_pos t
  have hq1 : leftNome t < 1 := (leftNome_lt_ten_neg_five ht htu).trans (by norm_num)
  have hκ := leftKappa_gt ht htu
  have hκ0 : 0 < leftKappa t := by linarith
  have hH : leftChordH (leftNome t) ≤ 2*leftNome t := by
    unfold leftChordH
    exact div_le_self (by positivity) (by nlinarith [sq_nonneg (leftNome t)])
  refine ⟨leftChordH_pos hq0, ?_, leftChordH_sq_add_K_sq _, ?_⟩
  · unfold leftChordK
    apply div_nonneg _ (by positivity)
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hH hκ0.le
    have hsmall := leftKappa_mul_nome_lt ht htu
    nlinarith

/-- The manuscript's comparison-period lower bound, for the actual vertical root branch. -/
theorem leftComparisonPeriod_lower_bound {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    (Real.pi/t)*(Real.exp (leftKappa t)/(16*(leftKappa t)^2)) ≤ leftComparisonPeriod t := by
  rcases actual_left_chord_parameters ht htu with ⟨hh,hk,hsq,hκh⟩
  have hJ := leftChordRealKernel_integral_lower (leftKappa_gt ht htu) hh hk hsq hκh
  calc
    _ = (Real.pi/(2*t))*(Real.exp (leftKappa t)/(8*(leftKappa t)^2)) := by ring
    _ ≤ (Real.pi/(2*t))*(∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
        leftChordRealKernel (leftKappa t) (leftChordH (leftNome t)) v) :=
      mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = leftComparisonPeriod t := (leftComparisonPeriod_eq_chord ht).symm

theorem leftComparisonPeriod_gt_seventy {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    (70 : ℝ)*(Real.pi/t) < leftComparisonPeriod t := by
  have he := comparison_exponential_lower_bound (leftKappa_gt ht htu)
  have hm := mul_lt_mul_of_pos_left he (div_pos Real.pi_pos ht)
  rw [mul_comm (Real.pi/t) 70] at hm
  exact hm.trans_le (leftComparisonPeriod_lower_bound ht htu)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftComparisonPeriod_lower_bound
#print axioms TwoAxisHelicoid.leftComparisonPeriod_gt_seventy
