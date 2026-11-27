import TwoAxisHelicoid.SeriesTail

namespace TwoAxisHelicoid

noncomputable def linearTail (q : ℝ) (N : ℕ) : ℝ :=
  q^(N+1)*(((N:ℝ)+1)/(1-q)+q/(1-q)^2)

noncomputable def cubicTail (q : ℝ) (N : ℕ) : ℝ :=
  q^(N+1)*(((N:ℝ)+1)^3/(1-q)+3*((N:ℝ)+1)^2*q/(1-q)^2+
    3*((N:ℝ)+1)*q*(1+q)/(1-q)^3+q*(1+4*q+q^2)/(1-q)^4)

theorem hasSum_cube_geometric {q : ℝ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (n:ℝ)^3*q^n) (q*(1+4*q+q^2)/(1-q)^4) := by
  have h := hasSum_pow_mul_geometric_of_norm_lt_one 3 hq
  have hn : 1-q ≠ 0 := by
    have hlt : q < 1 := lt_of_le_of_lt (le_abs_self q) (by simpa only [Real.norm_eq_abs] using hq)
    linarith
  convert h using 1
  norm_num [Finset.sum_range_succ,Nat.stirlingSecond] 
  field_simp
  ring

theorem hasSum_linear_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    HasSum (fun n : ℕ => ((n+N+1:ℕ):ℝ)*q^(n+N+1)) (linearTail q N) := by
  have hq : ‖q‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1
  have h0 := (hasSum_geometric_of_norm_lt_one hq).mul_left ((N:ℝ)+1)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hq
  convert (h0.add h1).mul_left (q^(N+1)) using 1
  · ext n
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show n+N+1 = n+(N+1) by omega,pow_add]
    ring
  · unfold linearTail
    ring

theorem hasSum_cubic_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    HasSum (fun n : ℕ => ((n+N+1:ℕ):ℝ)^3*q^(n+N+1)) (cubicTail q N) := by
  have hq : ‖q‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1
  have h0 := (hasSum_geometric_of_norm_lt_one hq).mul_left (((N:ℝ)+1)^3)
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hq).mul_left (3*((N:ℝ)+1)^2)
  have h2 := (hasSum_sq_mul_geometric_of_norm_lt_one hq).mul_left (3*((N:ℝ)+1))
  have h3 := hasSum_cube_geometric hq
  convert (((h0.add h1).add h2).add h3).mul_left (q^(N+1)) using 1
  · ext n
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show n+N+1 = n+(N+1) by omega,pow_add]
    ring
  · unfold cubicTail
    ring

theorem lambert_term_bound {Q q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hQ : |Q| ≤ q) (j : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    |(n:ℝ)^j*Q^n/(1-Q^n)| ≤ (n:ℝ)^j*q^n/(1-q) := by
  have hp : |Q^n| ≤ q^n := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg Q) hQ n
  have hpow : q^n ≤ q := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ]
    exact mul_le_of_le_one_left hq0 (pow_le_one₀ hq0 hq1.le)
  have hden : 1-q ≤ |1-Q^n| := by
    have h := le_abs_self (1-Q^n)
    have hQp := (le_abs_self (Q^n)).trans (hp.trans hpow)
    linarith
  have hpos : 0 < |1-Q^n| := (sub_pos.mpr hq1).trans_le hden
  rw [abs_div,abs_mul,abs_pow,abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    _ ≤ (n:ℝ)^j*q^n/|1-Q^n| :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) hpos.le
    _ ≤ (n:ℝ)^j*q^n/(1-q) :=
      div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hq1) hden

theorem lambert_tail_bound {Q q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hQ : |Q| ≤ q) (j N : ℕ) :
    |∑' n : ℕ, ((n+N+1:ℕ):ℝ)^j*Q^(n+N+1)/(1-Q^(n+N+1))| ≤
      (∑' n : ℕ, ((n+N+1:ℕ):ℝ)^j*q^(n+N+1))/(1-q) := by
  have hq : ‖q‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1
  have hs : Summable (fun n : ℕ => ((n+N+1:ℕ):ℝ)^j*q^(n+N+1)) :=
    (summable_pow_mul_geometric_of_norm_lt_one j hq).comp_injective
      (i := fun n : ℕ => n+N+1) (by intro m n h; dsimp only at h; omega)
  have hmajor := hs.div_const (1-q)
  have hbound (n : ℕ) := lambert_term_bound hq0 hq1 hQ j (show 1 ≤ n+N+1 by omega)
  have habs := Summable.of_nonneg_of_le (fun n => abs_nonneg _ ) hbound hmajor
  have hnorm : Summable (fun n : ℕ => ‖((n+N+1:ℕ):ℝ)^j*Q^(n+N+1)/(1-Q^(n+N+1))‖) := by
    simpa only [Real.norm_eq_abs] using habs
  calc
    _ ≤ ∑' n : ℕ, |((n+N+1:ℕ):ℝ)^j*Q^(n+N+1)/(1-Q^(n+N+1))| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ((n+N+1:ℕ):ℝ)^j*q^(n+N+1)/(1-q) := habs.tsum_le_tsum hbound hmajor
    _ = _ := tsum_div_const

theorem lambert_positive_series_summable {Q q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hQ : |Q| ≤ q) (j : ℕ) :
    Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^j*Q^(n+1)/(1-Q^(n+1))) := by
  have hq : ‖q‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1
  have hs : Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^j*q^(n+1)) :=
    (summable_pow_mul_geometric_of_norm_lt_one j hq).comp_injective
      (i := fun n : ℕ => n+1) (by intro m n h; dsimp only at h; omega)
  have hb (n : ℕ) : ‖((n+1:ℕ):ℝ)^j*Q^(n+1)/(1-Q^(n+1))‖ ≤
      ((n+1:ℕ):ℝ)^j*q^(n+1)/(1-q) := by
    simpa only [Real.norm_eq_abs] using lambert_term_bound hq0 hq1 hQ j (show 1 ≤ n+1 by omega)
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hs.div_const (1-q))).of_norm

theorem lambert_remainder_bound {Q q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hQ : |Q| ≤ q) (j N : ℕ) :
    |(∑' n : ℕ, ((n+1:ℕ):ℝ)^j*Q^(n+1)/(1-Q^(n+1)))-
      (∑ n ∈ Finset.range N, ((n+1:ℕ):ℝ)^j*Q^(n+1)/(1-Q^(n+1)))| ≤
      (∑' n : ℕ, ((n+N+1:ℕ):ℝ)^j*q^(n+N+1))/(1-q) := by
  have he := (lambert_positive_series_summable hq0 hq1 hQ j).sum_add_tsum_nat_add N
  rw [← he,add_sub_cancel_left]
  exact lambert_tail_bound hq0 hq1 hQ j N

theorem lambert_linear_tail_bound {Q q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hQ : |Q| ≤ q) (N : ℕ) :
    |∑' n : ℕ, ((n+N+1:ℕ):ℝ)*Q^(n+N+1)/(1-Q^(n+N+1))| ≤ linearTail q N/(1-q) := by
  simpa only [pow_one,(hasSum_linear_tail hq0 hq1 N).tsum_eq] using
    lambert_tail_bound hq0 hq1 hQ 1 N

theorem lambert_cubic_tail_bound {Q q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hQ : |Q| ≤ q) (N : ℕ) :
    |∑' n : ℕ, ((n+N+1:ℕ):ℝ)^3*Q^(n+N+1)/(1-Q^(n+N+1))| ≤ cubicTail q N/(1-q) := by
  simpa only [(hasSum_cubic_tail hq0 hq1 N).tsum_eq] using lambert_tail_bound hq0 hq1 hQ 3 N

theorem lambert_linear_remainder_bound {Q q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hQ : |Q| ≤ q) (N : ℕ) :
    |(∑' n : ℕ, ((n+1:ℕ):ℝ)*Q^(n+1)/(1-Q^(n+1)))-
      (∑ n ∈ Finset.range N, ((n+1:ℕ):ℝ)*Q^(n+1)/(1-Q^(n+1)))| ≤ linearTail q N/(1-q) := by
  simpa only [pow_one,(hasSum_linear_tail hq0 hq1 N).tsum_eq] using
    lambert_remainder_bound hq0 hq1 hQ 1 N

theorem lambert_cubic_remainder_bound {Q q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hQ : |Q| ≤ q) (N : ℕ) :
    |(∑' n : ℕ, ((n+1:ℕ):ℝ)^3*Q^(n+1)/(1-Q^(n+1)))-
      (∑ n ∈ Finset.range N, ((n+1:ℕ):ℝ)^3*Q^(n+1)/(1-Q^(n+1)))| ≤ cubicTail q N/(1-q) := by
  simpa only [(hasSum_cubic_tail hq0 hq1 N).tsum_eq] using
    lambert_remainder_bound hq0 hq1 hQ 3 N

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.lambert_linear_tail_bound
#print axioms TwoAxisHelicoid.lambert_cubic_tail_bound
