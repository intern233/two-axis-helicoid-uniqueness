import TwoAxisHelicoid.LeftNumericalConstants

namespace TwoAxisHelicoid
open Set
set_option maxHeartbeats 800000

theorem exp_half_lt_two : Real.exp (1/2) < (2 : ℝ) := by
  have he : (Real.exp (1/2))^2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1/2)]

theorem exp_two_lt_eight : Real.exp 2 < (8 : ℝ) := by
  have he : Real.exp 2 = (Real.exp 1)^2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  have hb : Real.exp 1 < (14/5 : ℝ) := by linarith [Real.exp_one_lt_d9]
  nlinarith [Real.exp_pos 1]

theorem mul_exp_neg_strictMono : StrictMonoOn (fun x : ℝ => x*Real.exp (-x)) (Iic 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _) (by fun_prop)
  intro x hx
  have hx1 : x < 1 := by simpa only [interior_Iic, mem_Iio] using hx
  have hd : HasDerivAt (fun y : ℝ => y*Real.exp (-y)) ((1-x)*Real.exp (-x)) x := by
    have h := (hasDerivAt_id x).mul ((hasDerivAt_id x).neg.exp)
    simp only [Pi.neg_apply, id_eq] at h
    convert h using 1
    · rfl
    · ring
  rw [hd.deriv]
  exact mul_pos (by linarith) (Real.exp_pos _)

theorem x_mul_exp_neg_gt_quarter {x : ℝ} (hl : 1/2 ≤ x) (hu : x ≤ 2) :
    (1/4 : ℝ) < x*Real.exp (-x) := by
  have hleft : (1/4 : ℝ) < (1/2)*Real.exp (-(1/2)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (lt_div_iff₀ (Real.exp_pos _)).mpr
    linarith [exp_half_lt_two]
  have hright : (1/4 : ℝ) < 2*Real.exp (-2) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (lt_div_iff₀ (Real.exp_pos _)).mpr
    linarith [exp_two_lt_eight]
  by_cases hx : x ≤ 1
  · exact hleft.trans_le (mul_exp_neg_strictMono.monotoneOn
      (by norm_num : (1/2 : ℝ) ∈ Iic 1) hx hl)
  · exact hright.trans_le (mul_exp_neg_strictAnti.antitoneOn
      (show x ∈ Ici 1 by change 1 ≤ x; linarith) (by norm_num : (2 : ℝ) ∈ Ici 1) hu)

theorem shifted_exponential_lower {k v : ℝ} (hk : 0 < k)
    (hvl : -1+1/(2*k) ≤ v) (hvu : v ≤ -1+2/k) :
    Real.exp k/(4*k) < (v+1)*Real.exp (-k*v) := by
  have hl : (1/2 : ℝ) ≤ k*(v+1) := by
    have h := (div_le_iff₀ (show 0 < 2*k by positivity)).mp (show 1/(2*k) ≤ v+1 by linarith)
    nlinarith
  have hu : k*(v+1) ≤ 2 := by
    have h := (le_div_iff₀ hk).mp (show v+1 ≤ 2/k by linarith)
    nlinarith
  have h := mul_lt_mul_of_pos_left (x_mul_exp_neg_gt_quarter hl hu)
    (div_pos (Real.exp_pos k) hk)
  have he : Real.exp k/k*(k*(v+1)*Real.exp (-(k*(v+1)))) =
      (v+1)*Real.exp (-k*v) := by
    rw [show -(k*(v+1)) = -k*v-k by ring, Real.exp_sub]
    field_simp [hk.ne', Real.exp_ne_zero k]
  convert h using 1
  · ring
  · exact he.symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.shifted_exponential_lower
