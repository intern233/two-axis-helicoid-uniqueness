import TwoAxisHelicoid.LeftRootParameters

namespace TwoAxisHelicoid
set_option maxHeartbeats 1200000

/-- Uniform second-order expansion of the elementary Jacobi fraction. -/
theorem jacobiFraction_second_remainder {x : ℝ} (hx : |x| ≤ 1/50) :
    |jacobiFraction x-x-2*x^2| ≤ 4*|x|^3 := by
  have hb := abs_le.mp hx
  have hd : 0 < (1-x)^2 := sq_pos_of_pos (by linarith)
  have he : jacobiFraction x-x-2*x^2 = x^3*((3-2*x)/(1-x)^2) := by
    unfold jacobiFraction
    field_simp [show 1-x ≠ 0 by linarith]
    ring
  have hc0 : 0 ≤ (3-2*x)/(1-x)^2 := div_nonneg (by linarith) hd.le
  have hc : (3-2*x)/(1-x)^2 ≤ 4 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg x]
  rw [he,abs_mul,abs_pow,abs_of_nonneg hc0]
  exact (mul_le_mul_of_nonneg_left hc (pow_nonneg (abs_nonneg x) 3)).trans_eq (mul_comm _ _)

/-- The actual vertical equation determines the quadratic difference of its
reciprocal roots, with a uniform cubic remainder. -/
theorem jacobi_root_second_balance {q r : ℝ} (hq0 : 0 < q) (hq : q ≤ 1/100)
    (hrl : q/2 ≤ r) (hru : r ≤ q) (hroot : jacobiRealE (-q^2) r = 0) :
    |q^2/r-r-4*q^2| ≤ 50*q^3 := by
  let b := q^2/r
  obtain ⟨hr,hbl,hbu⟩ := jacobi_root_basic_bounds hq0 hrl hru
  have hb0 : 0 < b := lt_of_lt_of_le hq0 hbl
  have hbr : b*r = q^2 := by dsimp [b]; field_simp
  have he := jacobiRealE_split_root hq0 hq hrl hru
  rw [hroot] at he
  have hf : jacobiFraction (-b) = -b/(1+b)^2 := by
    unfold jacobiFraction
    congr 1
    ring
  have hsplit : b-r-2*(r^2+b^2) =
      (jacobiFraction r-r-2*r^2)+(jacobiFraction (-b)+b-2*b^2)+
        jacobiRootRemainder q r := by
    rw [hf]
    dsimp [b] at *
    linear_combination he
  have hR := jacobiFraction_second_remainder
    (x := r) (by rw [abs_of_pos hr]; linarith)
  have hB := jacobiFraction_second_remainder
    (x := -b) (by rw [abs_neg,abs_of_pos hb0]; dsimp [b]; linarith)
  simp only [sub_neg_eq_add,neg_sq,abs_neg,abs_of_pos hb0] at hB
  rw [abs_of_pos hr] at hR
  have hT := (jacobiRootRemainder_abs_lt hq0 hq hrl hru).le
  have hr3 := pow_le_pow_left₀ hr.le hru 3
  have hb3 := pow_le_pow_left₀ hb0.le hbu 3
  have hsmall : |b-r-2*(r^2+b^2)| ≤ 40*q^3 := by
    rw [hsplit]
    have htriangle := (abs_add_le
      ((jacobiFraction r-r-2*r^2)+(jacobiFraction (-b)+b-2*b^2))
      (jacobiRootRemainder q r)).trans
      (add_le_add (abs_add_le
        (jacobiFraction r-r-2*r^2) (jacobiFraction (-b)+b-2*b^2))
        (le_refl |jacobiRootRemainder q r|))
    nlinarith only [htriangle,hR,hB,hT,hr3,hb3]
  have hd := jacobi_root_beta_sub_r_le hq0 hq hrl hru hroot
  have hdelta2 := pow_le_pow_left₀ hd.1 hd.2 2
  have hq4 := mul_le_mul_of_nonneg_left hq (pow_nonneg hq0.le 3)
  have hsame : b-r-4*q^2 = (b-r-2*(r^2+b^2))+2*(b-r)^2 := by nlinarith only [hbr]
  rw [hsame]
  have htriangle := abs_add_le (b-r-2*(r^2+b^2)) (2*(b-r)^2)
  rw [abs_of_nonneg (by positivity : 0 ≤ 2*(b-r)^2)] at htriangle
  dsimp [b] at *
  nlinarith only [htriangle,hsmall,hdelta2,hq4,pow_pos hq0 3]

theorem sinh_sub_self_abs_le_square {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sinh x-x| ≤ x^2 := by
  have hp := abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)
  have hm := abs_le.mp (Real.abs_exp_sub_one_sub_id_le
    (x := -x) (by simpa only [abs_neg] using hx))
  rw [Real.sinh_eq]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The logarithmic root displacement equals twice the half-nome, to second
order. All bounds come from the actual infinite Jacobi equation. -/
theorem jacobi_root_log_second_remainder {q r : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1/100) (hrl : q/2 < r) (hru : r < q)
    (hroot : jacobiRealE (-q^2) r = 0) :
    |Real.log (q/r)-2*q| ≤ 64*q^2 := by
  have hr : 0 < r := lt_trans (by positivity) hrl
  have he := jacobi_root_log_ratio_bound hq0 hq hrl hru hroot
  have hs : 2*q*Real.sinh (Real.log (q/r)) = q^2/r-r := by
    rw [Real.sinh_eq,Real.exp_neg,Real.exp_log (div_pos hq0 hr)]
    field_simp
  have hb := jacobi_root_second_balance hq0 hq hrl.le hru.le hroot
  have hb' : |Real.sinh (Real.log (q/r))-2*q| ≤ 25*q^2 := by
    have hid : q^2/r-r-4*q^2 = 2*q*(Real.sinh (Real.log (q/r))-2*q) := by
      rw [mul_sub,hs]
      ring
    rw [hid,abs_mul,abs_of_pos (by positivity : 0 < 2*q)] at hb
    by_contra hn
    have hp := mul_pos (show 0 < 2*q by positivity)
      (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith only [hb,hp]
  have ht := sinh_sub_self_abs_le_square
    (x := Real.log (q/r)) (by rw [abs_of_pos he.1]; linarith)
  have he2 := pow_le_pow_left₀ he.1.le he.2 2
  have htriangle := abs_sub_le (Real.log (q/r)) (Real.sinh (Real.log (q/r))) (2*q)
  rw [abs_sub_comm (Real.log (q/r)) (Real.sinh (Real.log (q/r)))] at htriangle
  nlinarith only [htriangle,ht,hb',he2,sq_nonneg q]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.jacobi_root_log_second_remainder
