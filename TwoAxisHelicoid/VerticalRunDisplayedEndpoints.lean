import TwoAxisHelicoid.VerticalRunRationalEnclosure
import TwoAxisHelicoid.VerticalRunArithmetic
import TwoAxisHelicoid.EllipticVerticalDomain

namespace TwoAxisHelicoid.VerticalRun

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem left_normalized_F :
    (-47221253557264140850267997705597 / 10^40 : ℝ) < ellipticFReal (70945978 / 10^8) / Real.pi^2 ∧
      ellipticFReal (70945978 / 10^8) / Real.pi^2 < (-47221253557264140850240321370933 / 10^40 : ℝ) := by
  have h := displayed_bound_of_tests (t := 70945978 / 10^8)
    (lo := 10765392093268113736230733970338727 / 10^35) (hi := 10765392093268113736230733970338728 / 10^35)
    (L := -47221253557264140850267997705597 / 10^40) (U := -47221253557264140850240321370933 / 10^40)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    left_display_tests.1 left_display_tests.2
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one,
    Rat.cast_zero] using h

theorem right_normalized_F :
    (13998405173549555596490797567326 / 10^39 : ℝ) < ellipticFReal (70945980 / 10^8) / Real.pi^2 ∧
      ellipticFReal (70945980 / 10^8) / Real.pi^2 < (13998405173549555596493565200718 / 10^39 : ℝ) := by
  have h := displayed_bound_of_tests (t := 70945980 / 10^8)
    (lo := 10765391416858600721767478766631171 / 10^35) (hi := 10765391416858600721767478766631172 / 10^35)
    (L := 13998405173549555596490797567326 / 10^39) (U := 13998405173549555596493565200718 / 10^39)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    right_display_tests.1 right_display_tests.2
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one,
    Rat.cast_zero] using h

private theorem innerLeft_normalized_F :
    (-1 / 10^7 : ℝ) < ellipticFReal (709459781 / 10^9) / Real.pi^2 ∧
      ellipticFReal (709459781 / 10^9) / Real.pi^2 < (0 : ℝ) := by
  have h := displayed_bound_of_tests (t := 709459781 / 10^9)
    (lo := 10765392059447637076131062167372461 / 10^35) (hi := 10765392059447637076131062167372462 / 10^35)
    (L := -1 / 10^7) (U := 0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    left_inner_tests.1 left_inner_tests.2
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one,
    Rat.cast_zero] using h

private theorem innerRight_normalized_F :
    (0 : ℝ) < ellipticFReal (709459799 / 10^9) / Real.pi^2 ∧
      ellipticFReal (709459799 / 10^9) / Real.pi^2 < (1 / 10^7 : ℝ) := by
  have h := displayed_bound_of_tests (t := 709459799 / 10^9)
    (lo := 10765391450679075363114151510334436 / 10^35) (hi := 10765391450679075363114151510334437 / 10^35)
    (L := 0) (U := 1 / 10^7)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    right_inner_tests.1 right_inner_tests.2
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one,
    Rat.cast_zero] using h

/-- The two interior test points establish a strict margin that exceeds the
round-to-nearest displacement of both printed reciprocal endpoints. -/
theorem critical_inner_bracket :
    (709459781 / 10^9 : ℝ) < ellipticCriticalT ∧ ellipticCriticalT < 709459799 / 10^9 := by
  have hL := (div_lt_iff₀ (sq_pos_of_pos Real.pi_pos)).mp innerLeft_normalized_F.2
  have hR := (lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mp innerRight_normalized_F.1
  exact ⟨(ellipticFReal_neg_iff (by norm_num)).mp (by simpa using hL),
    (ellipticFReal_pos_iff (by norm_num)).mp (by simpa using hR)⟩

/-- The strict displayed enclosure in the `T_* interval` line of vertical_run.log. -/
theorem displayed_Tstar :
    14095231329527057065107846843472 / 10^31 < ellipticVerticalUpper ∧
      ellipticVerticalUpper < 14095231726878160732381474817360 / 10^31 := by
  have low := one_div_lt_one_div_of_lt ellipticCriticalT_pos critical_inner_bracket.2
  have high := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 709459781 / 10^9)
    critical_inner_bracket.1
  exact ⟨lt_trans (by norm_num) low, lt_trans high (by norm_num)⟩

end TwoAxisHelicoid.VerticalRun

#print axioms TwoAxisHelicoid.VerticalRun.left_normalized_F
#print axioms TwoAxisHelicoid.VerticalRun.right_normalized_F
#print axioms TwoAxisHelicoid.VerticalRun.displayed_Tstar
