import TwoAxisHelicoid.JacobiEllipticIdentity

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000

noncomputable def jacobiFraction (x : ℝ) : ℝ := x/(1-x)^2

noncomputable def jacobiGeometricSeries (Q a : ℝ) : ℝ :=
  ∑' n : ℕ, jacobiFraction (Q^n*a)

noncomputable def jacobiRealE (Q r : ℝ) : ℝ :=
  jacobiFraction r+jacobiGeometricSeries Q (Q*r)+jacobiGeometricSeries Q (Q/r)

theorem jacobiFraction_abs_le {x r : ℝ} (hr : r < 1) (hx : |x| ≤ r) :
    |jacobiFraction x| ≤ |x|/(1-r)^2 := by
  have hd : 1-r ≤ |1-x| := by
    have h1 := le_abs_self (1-x)
    have h2 := (le_abs_self x).trans hx
    linarith
  rw [jacobiFraction, abs_div, abs_pow]
  exact div_le_div_of_nonneg_left (abs_nonneg x) (sq_pos_of_pos (sub_pos.mpr hr))
    (pow_le_pow_left₀ (sub_pos.mpr hr).le hd 2)

theorem jacobi_geometric_argument_abs_le {Q a : ℝ} (hQ : |Q| < 1) (n : ℕ) :
    |Q^n*a| ≤ |a| := by
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_left (abs_nonneg a) (pow_le_one₀ (abs_nonneg Q) hQ.le)

theorem jacobi_geometric_term_abs_le {Q a : ℝ} (hQ : |Q| < 1) (ha : |a| < 1) (n : ℕ) :
    |jacobiFraction (Q^n*a)| ≤ |Q|^n*|a|/(1-|a|)^2 := by
  simpa only [abs_mul, abs_pow] using
    jacobiFraction_abs_le ha (jacobi_geometric_argument_abs_le hQ n)

theorem jacobiGeometricSeries_summable {Q a : ℝ} (hQ : |Q| < 1) (ha : |a| < 1) :
    Summable (fun n : ℕ => jacobiFraction (Q^n*a)) := by
  have hs := ((summable_geometric_of_lt_one (abs_nonneg Q) hQ).mul_right |a|).div_const ((1-|a|)^2)
  apply Summable.of_norm_bounded hs
  intro n
  simpa only [Real.norm_eq_abs] using jacobi_geometric_term_abs_le hQ ha n

theorem jacobiGeometricSeries_abs_le {Q a : ℝ} (hQ : |Q| < 1) (ha : |a| < 1) :
    |jacobiGeometricSeries Q a| ≤ |a|/((1-|Q|)*(1-|a|)^2) := by
  have hs := ((summable_geometric_of_lt_one (abs_nonneg Q) hQ).mul_right |a|).div_const ((1-|a|)^2)
  have hn : Summable (fun n : ℕ => |jacobiFraction (Q^n*a)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (jacobi_geometric_term_abs_le hQ ha) hs
  have hnorm : Summable (fun n : ℕ => ‖jacobiFraction (Q^n*a)‖) := by
    simpa only [Real.norm_eq_abs] using hn
  calc
    _ ≤ ∑' n : ℕ, |jacobiFraction (Q^n*a)| := by
      simpa only [jacobiGeometricSeries, Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, |Q|^n*|a|/(1-|a|)^2 := hn.tsum_le_tsum (jacobi_geometric_term_abs_le hQ ha) hs
    _ = _ := by
      rw [tsum_div_const, tsum_mul_right,
        tsum_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs, abs_abs] using hQ)]
      field_simp

theorem jacobiGeometricSeries_split {Q a : ℝ} (hQ : |Q| < 1) (ha : |a| < 1) :
    jacobiGeometricSeries Q a = jacobiFraction a+jacobiGeometricSeries Q (Q*a) := by
  have h := (jacobiGeometricSeries_summable hQ ha).sum_add_tsum_nat_add 1
  simpa [jacobiGeometricSeries, Finset.sum_range_succ, pow_succ, mul_assoc] using h.symm

theorem jacobiSecondE_ofReal (Q r : ℝ) :
    jacobiSecondE (Q : ℂ) (r : ℂ) = (jacobiRealE Q r : ℝ) := by
  simp only [jacobiSecondE, jacobiSecondSum, jacobiRealE, jacobiGeometricSeries,
    jacobiFraction, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_tsum]
  congr 2
  · apply tsum_congr
    intro n
    rw [pow_succ]
    ring
  · funext n
    rw [pow_succ]
    ring

theorem jacobiFraction_pair {x : ℝ} (hx : |x| < 1) :
    jacobiFraction x+jacobiFraction (-x) = 4*x^2/(1-x^2)^2 := by
  have ha := abs_lt.mp hx
  have h1 : 1-x ≠ 0 := by linarith
  have h2 : 1+x ≠ 0 := by linarith
  have h3 : 1-x^2 ≠ 0 := by nlinarith [sq_abs x]
  unfold jacobiFraction
  rw [sub_neg_eq_add]
  field_simp [h1, h2, h3]
  ring

/-- Exact pairing proves the sign at `r = q` for every real nome `0 < q < 1`. -/
theorem jacobiRealE_at_q_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < jacobiRealE (-q^2) q := by
  have hQ : |-q^2| < 1 := by rw [abs_neg, abs_sq]; nlinarith
  have hq : |q| < 1 := by simpa only [abs_of_pos hq0] using hq1
  have hnq : |-q| < 1 := by simpa only [abs_neg] using hq
  have hs1 := jacobiGeometricSeries_summable hQ hq
  have hs2 := jacobiGeometricSeries_summable hQ hnq
  have he : jacobiRealE (-q^2) q =
      ∑' n : ℕ, (jacobiFraction ((-q^2)^n*q)+jacobiFraction ((-q^2)^n*(-q))) := by
    unfold jacobiRealE
    rw [show -q^2/q = -q by field_simp]
    rw [← jacobiGeometricSeries_split hQ hq]
    exact (hs1.tsum_add hs2).symm
  rw [he]
  refine (hs1.add hs2).tsum_pos ?_ 0 ?_
  · intro n
    have hb := (jacobi_geometric_argument_abs_le (a := q) hQ n).trans_lt hq
    rw [show (-q^2)^n*(-q) = -((-q^2)^n*q) by ring, jacobiFraction_pair hb]
    positivity
  · norm_num only [pow_zero, one_mul]
    rw [jacobiFraction_pair hq]
    have hd : 0 < 1-q^2 := by nlinarith
    exact div_pos (by positivity) (sq_pos_of_pos hd)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiGeometricSeries_abs_le
#print axioms TwoAxisHelicoid.jacobiRealE_at_q_pos
