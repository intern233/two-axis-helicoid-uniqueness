import TwoAxisHelicoid.ThetaConvergence

/-! The explicit uniform theta derivative remainder bound, Lemma 8.1. -/

namespace TwoAxisHelicoid

noncomputable def thetaPartial (t : ℝ) (j N : ℕ) (v : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, thetaTerm t j n v

theorem thetaPartial_hasDerivAt (t : ℝ) (j N : ℕ) (v : ℂ) :
    HasDerivAt (thetaPartial t j N) (thetaPartial t (j+1) N v) v :=
  HasDerivAt.fun_sum (fun n _ => hasDerivAt_thetaTerm t j n v)

theorem thetaPartial_iteratedDeriv (t : ℝ) (j N : ℕ) :
    iteratedDeriv j (thetaPartial t 0 N) = thetaPartial t j N := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    exact funext (fun v => (thetaPartial_hasDerivAt t j N v).deriv)

noncomputable def thetaRatio (t y : ℝ) (j N : ℕ) : ℝ :=
  ((2 * N + 3 : ℝ) / (2 * N + 1))^j *
    Real.exp (-Real.pi * t * (N+1) + 2*y)

theorem thetaRatio_nonneg (t y : ℝ) (j N : ℕ) : 0 ≤ thetaRatio t y j N := by
  unfold thetaRatio
  positivity

theorem thetaMajorant_succ (t y : ℝ) (j n : ℕ) :
    thetaMajorant t y j (n+1) = thetaMajorant t y j n * thetaRatio t y j n := by
  have hden : (2 * n + 1 : ℝ) ≠ 0 := by positivity
  have he : -Real.pi*t*((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+1)/2 +
      (2*((n+1 : ℕ) : ℝ)+1)*y =
      (-Real.pi*t*n*(n+1)/2+(2*n+1)*y) + (-Real.pi*t*(n+1)+2*y) := by
    push_cast
    ring
  unfold thetaMajorant thetaRatio
  rw [he, Real.exp_add, div_pow]
  push_cast
  have hk : (2 * ((n : ℝ)+1) + 1) = 2*n+3 := by ring
  rw [hk]
  field_simp

theorem thetaRatio_antitone {t : ℝ} (ht : 0 < t) (y : ℝ) (j : ℕ) :
    Antitone (thetaRatio t y j) := by
  intro N n hN
  have hNr : (N : ℝ) ≤ n := by exact_mod_cast hN
  have hfrac : (2 * n + 3 : ℝ) / (2*n+1) ≤ (2*N+3)/(2*N+1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hpow : ((2*n+3 : ℝ)/(2*n+1))^j ≤ ((2*N+3)/(2*N+1))^j := by
    gcongr
  have hexp : Real.exp (-Real.pi*t*(n+1)+2*y) ≤
      Real.exp (-Real.pi*t*(N+1)+2*y) := by
    apply Real.exp_le_exp.mpr
    have hprod : 0 ≤ Real.pi*t*((n : ℝ)-N) := by positivity
    nlinarith
  exact mul_le_mul hpow hexp (Real.exp_nonneg _) (by positivity)

theorem thetaMajorant_shift_bound {t : ℝ} (ht : 0 < t) (y : ℝ) (j N k : ℕ) :
    thetaMajorant t y j (N+k) ≤ thetaMajorant t y j N * (thetaRatio t y j N)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show N+(k+1) = (N+k)+1 by omega, thetaMajorant_succ, pow_succ]
    calc
      thetaMajorant t y j (N+k) * thetaRatio t y j (N+k) ≤
          thetaMajorant t y j (N+k) * thetaRatio t y j N :=
        mul_le_mul_of_nonneg_left ((thetaRatio_antitone ht y j) (by omega))
          (thetaMajorant_nonneg _ _ _ _)
      _ ≤ (thetaMajorant t y j N * thetaRatio t y j N^k) * thetaRatio t y j N :=
        mul_le_mul_of_nonneg_right ih (thetaRatio_nonneg _ _ _ _)
      _ = _ := by ring

/-- The complex disk bound applies uniformly on every parameter and argument box. -/
theorem thetaJet_tail_bound {t tlo y : ℝ} (htlo : 0 < tlo) (ht : tlo ≤ t)
    {v : ℂ} (hv : |v.im| ≤ y) (j N : ℕ) (hr : thetaRatio tlo y j N < 1) :
    ‖thetaJet t j v - ∑ n ∈ Finset.range N, thetaTerm t j n v‖ ≤
      thetaMajorant tlo y j N / (1 - thetaRatio tlo y j N) := by
  have hr0 := thetaRatio_nonneg tlo y j N
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr).mul_left (thetaMajorant tlo y j N)
  have hb : ∀ k : ℕ, ‖thetaTerm t j (k+N) v‖ ≤
      thetaMajorant tlo y j N * thetaRatio tlo y j N^k := by
    intro k
    exact (thetaTerm_norm_le ht hv j (k+N)).trans
      (by simpa only [Nat.add_comm] using thetaMajorant_shift_bound htlo y j N k)
  have hnorm := Summable.of_nonneg_of_le (fun k => norm_nonneg _) hb hgeom.summable
  have hsplit := (thetaTerm_summable (htlo.trans_le ht) j v).sum_add_tsum_nat_add N
  have heq : thetaJet t j v - ∑ n ∈ Finset.range N, thetaTerm t j n v =
      ∑' k : ℕ, thetaTerm t j (k+N) v := by
    unfold thetaJet
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hsplit.symm)
  rw [heq]
  calc
    _ ≤ ∑' k : ℕ, ‖thetaTerm t j (k+N) v‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, thetaMajorant tlo y j N * thetaRatio tlo y j N^k :=
      hnorm.tsum_le_tsum hb hgeom.summable
    _ = _ := by rw [hgeom.tsum_eq]; rfl

theorem theta_derivative_tail_bound {t tlo y : ℝ} (htlo : 0 < tlo) (ht : tlo ≤ t)
    {v : ℂ} (hv : |v.im| ≤ y) (j N : ℕ) (hr : thetaRatio tlo y j N < 1) :
    ‖iteratedDeriv j (thetaJet t 0) v - ∑ n ∈ Finset.range N, thetaTerm t j n v‖ ≤
      thetaMajorant tlo y j N / (1 - thetaRatio tlo y j N) := by
  rw [thetaJet_iteratedDeriv (htlo.trans_le ht)]
  exact thetaJet_tail_bound htlo ht hv j N hr

/-- Lemma 8.1 in exactly the form of derivatives of the series and its partial sum. -/
theorem theta_full_derivative_tail_bound {t tlo y : ℝ} (htlo : 0 < tlo) (ht : tlo ≤ t)
    {v : ℂ} (hv : |v.im| ≤ y) (j N : ℕ) (hr : thetaRatio tlo y j N < 1) :
    ‖iteratedDeriv j (thetaJet t 0) v - iteratedDeriv j (thetaPartial t 0 N) v‖ ≤
      thetaMajorant tlo y j N / (1 - thetaRatio tlo y j N) := by
  rw [thetaPartial_iteratedDeriv]
  exact theta_derivative_tail_bound htlo ht hv j N hr

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.theta_derivative_tail_bound
