import TwoAxisHelicoid.LeftMomentEstimates

namespace TwoAxisHelicoid
open Set

/-- The intermediate printed rational majorant retained in the estimate
of the coefficient of the horizontal error on the original small interval. -/
theorem left_error_printed_rational_chain {t : ℝ} (ht : 0<t) (ht' : t≤1/8) :
    let k := leftKappa t
    100*k*leftNome t*leftKappa0 t ≤ 100*k*(k+1)*Real.exp (-k) ∧
      100*k*(k+1)*Real.exp (-k) <
        100*(25/2:ℝ)*(27/2)/((3/2:ℝ)*7^6) ∧
      100*(25/2:ℝ)*(27/2)/((3/2:ℝ)*7^6) < 1 := by
  let k := leftKappa t
  have large : 25/2 < k := leftKappa_gt ht ht'
  have kpos : 0 < k := by linarith
  have qpos := leftNome_pos t
  have k0 := (leftKappa_bounds ht (by linarith)).2.2
  have qb := (leftBeta_bounds ht (by linarith)).1
  rw [←exp_neg_leftKappa] at qb
  have dec := quad_mul_exp_neg_strictAnti (show (25/2:ℝ) ∈ Ici 3 by norm_num)
    (show k ∈ Ici 3 by change 3≤k; linarith) large
  change k*(k+1)*Real.exp (-k) < (25/2:ℝ)*(25/2+1)*Real.exp (-(25/2)) at dec
  have rational : (25/2:ℝ)*(25/2+1)*Real.exp (-(25/2)) <
      (25/2:ℝ)*(27/2)/((3/2:ℝ)*7^6) := by
    rw [Real.exp_neg,←div_eq_mul_inv]
    rw [show (25/2:ℝ)+1 = 27/2 by norm_num]
    exact div_lt_div_of_pos_left (by norm_num) (by norm_num) exp_twenty_five_halves_gt
  refine ⟨?_,?_,by norm_num⟩
  · calc
      100*k*leftNome t*leftKappa0 t ≤ 100*k*leftNome t*(k+1) :=
        mul_le_mul_of_nonneg_left k0.le (by positivity)
      _ ≤ 100*k*(k+1)*Real.exp (-k) := by
        have h := mul_le_mul_of_nonneg_left qb (show 0 ≤ 100*k*(k+1) by positivity)
        simpa only [mul_assoc,mul_left_comm,mul_comm] using h
  · convert mul_lt_mul_of_pos_left (dec.trans rational) (by norm_num : (0:ℝ)<100) using 1 <;> ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.left_error_printed_rational_chain
