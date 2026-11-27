module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace TwoAxisHelicoid

/-- A Gaussian majorant for the first moment density on the positive half of the path. -/
theorem small_rho_first_weight_upper {κ b r x : ℝ} (hk : 0 ≤ κ) (hb : 0 ≤ b)
    (hr : r ≤ b) (hx : 0 < x) (hu : x ≤ 1) :
    ((x/(1+x^2))*Real.exp (κ*((1-x^2)/(1+x^2))))*(b/x+r*x) ≤ (b*Real.exp κ)*Real.exp (-κ*x^2) := by
  have den : 0 < 1+x^2 := by positivity
  have ratio : (b+r*x^2)/(1+x^2) ≤ b := by
    apply (div_le_iff₀ den).mpr
    nlinarith [mul_le_mul_of_nonneg_right hr (sq_nonneg x)]
  have e : Real.exp (κ*((1-x^2)/(1+x^2))) ≤ Real.exp κ*Real.exp (-κ*x^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : x^2 ≤ 1 := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hu)]
    have hr' := div_le_self (show 0 ≤ 1-x^2 by linarith) (show 1 ≤ 1+x^2 by linarith [sq_nonneg x])
    nlinarith only [mul_le_mul_of_nonneg_left hr' hk]
  have eq : ((x/(1+x^2))*Real.exp (κ*((1-x^2)/(1+x^2))))*(b/x+r*x) =
      ((b+r*x^2)/(1+x^2))*Real.exp (κ*((1-x^2)/(1+x^2))) := by
    field_simp [hx.ne',den.ne']
  calc
    _ = _ := eq
    _ ≤ b*(Real.exp κ*Real.exp (-κ*x^2)) := mul_le_mul ratio e (Real.exp_pos _).le hb
    _ = _ := by ring

/-- The second moment density is bounded by an integrable multiple of 1/x away from zero. -/
theorem small_rho_second_weight_upper {κ b r x : ℝ} (hk : 1 ≤ κ) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hrb : r ≤ b) (hx : 0 < x) (hu : x ≤ 1) :
    ((x/(1+x^2))*Real.exp (κ*((1-x^2)/(1+x^2))))*(b/x+r*x)^2 ≤ (Real.exp κ*b^2)*(1/x) := by
  have h1 := small_rho_first_weight_upper (by linarith : 0 ≤ κ) hb hrb hx hu
  have hB : b/x+r*x ≤ (b/x)*(1+x^2) := by
    have eq : (b/x)*(1+x^2) = b/x+b*x := by field_simp [hx.ne']
    rw [eq]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hrb hx.le)
  have step := mul_le_mul h1 hB (show 0 ≤ b/x+r*x by positivity)
    (show 0 ≤ (b*Real.exp κ)*Real.exp (-κ*x^2) by positivity)
  have sqle : 1+x^2 ≤ Real.exp (κ*x^2) := by
    have h := mul_le_mul_of_nonneg_right hk (sq_nonneg x)
    linarith only [h,Real.add_one_le_exp (κ*x^2)]
  have cut : (1+x^2)*Real.exp (-κ*x^2) ≤ 1 := by
    calc
      _ ≤ Real.exp (κ*x^2)*Real.exp (-κ*x^2) :=
        mul_le_mul_of_nonneg_right sqle (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp [neg_mul]
  calc
    _ = (((x/(1+x^2))*Real.exp (κ*((1-x^2)/(1+x^2))))*(b/x+r*x))*(b/x+r*x) := by ring
    _ ≤ _ := step
    _ = ((Real.exp κ*b^2)*(1/x))*((1+x^2)*Real.exp (-κ*x^2)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) cut

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.small_rho_first_weight_upper
#print axioms TwoAxisHelicoid.small_rho_second_weight_upper
