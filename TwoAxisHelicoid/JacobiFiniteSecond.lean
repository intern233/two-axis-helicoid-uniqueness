import TwoAxisHelicoid.JacobiRealSeries

namespace TwoAxisHelicoid
set_option maxHeartbeats 800000

noncomputable def jacobiFiniteSecond (Q a : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, jacobiFraction (Q^n*a)

theorem jacobiGeometricSeries_finite_split {Q a : ℝ} (hQ : |Q| < 1) (ha : |a| < 1) (N : ℕ) :
    jacobiGeometricSeries Q a = jacobiFiniteSecond Q a N+jacobiGeometricSeries Q (Q^N*a) := by
  have h := (jacobiGeometricSeries_summable hQ ha).sum_add_tsum_nat_add N
  have he : (∑' n : ℕ, jacobiFraction (Q^(n+N)*a)) = jacobiGeometricSeries Q (Q^N*a) := by
    unfold jacobiGeometricSeries
    apply tsum_congr
    intro n
    congr 1
    rw [pow_add]
    ring
  rw [he] at h
  exact h.symm

theorem jacobiGeometricSeries_finite_error {Q a : ℝ} {N : ℕ} {σ τ : ℝ}
    (hσ : |Q| ≤ σ) (hσ1 : σ < 1) (ha : |a| < 1)
    (hτ : |Q^N*a| ≤ τ) (hτ1 : τ < 1) :
    |jacobiGeometricSeries Q a-jacobiFiniteSecond Q a N| ≤
      τ/((1-σ)*(1-τ)^2) := by
  have hQ : |Q| < 1 := hσ.trans_lt hσ1
  have ht : |Q^N*a| < 1 := hτ.trans_lt hτ1
  have hτ0 : 0 ≤ τ := (abs_nonneg _).trans hτ
  rw [jacobiGeometricSeries_finite_split hQ ha N, add_sub_cancel_left]
  have h := jacobiGeometricSeries_abs_le hQ ht
  have hd0 : 0 < (1-σ)*(1-τ)^2 := mul_pos (sub_pos.mpr hσ1) (sq_pos_of_pos (sub_pos.mpr hτ1))
  have hd : (1-σ)*(1-τ)^2 ≤ (1-|Q|)*(1-|Q^N*a|)^2 :=
    mul_le_mul (by linarith)
      (pow_le_pow_left₀ (sub_pos.mpr hτ1).le (by linarith) 2)
      (sq_nonneg _) (sub_pos.mpr hQ).le
  apply h.trans
  exact (div_le_div_of_nonneg_right hτ (hd0.trans_le hd).le).trans
    (div_le_div_of_nonneg_left hτ0 hd0 hd)

theorem jacobiRealE_two_series {Q r : ℝ} (hQ : |Q| < 1) (hr : |r| < 1) :
    jacobiRealE Q r = jacobiGeometricSeries Q r+jacobiGeometricSeries Q (Q/r) := by
  unfold jacobiRealE
  rw [← jacobiGeometricSeries_split hQ hr]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiGeometricSeries_finite_error
