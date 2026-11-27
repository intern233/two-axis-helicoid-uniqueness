import TwoAxisHelicoid.JacobiProductEstimates

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 400000

theorem jacobi_factor_norm_le {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) (n : ℕ) :
    ‖q^(n+1)*x‖ ≤ ‖q‖*‖x‖ := by
  rw [norm_mul, norm_pow, pow_succ]
  have hn : ‖q‖^n ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
  simpa only [one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hn (mul_nonneg (norm_nonneg q) (norm_nonneg x))

theorem jacobi_factor_denominator_bound {q : ℂ} (hq : ‖q‖ < 1) (x : ℂ) (n : ℕ) :
    1-‖q‖*‖x‖ ≤ ‖1-q^(n+1)*x‖ := by
  have hn := jacobi_factor_norm_le hq x n
  have hd := norm_sub_norm_le (1 : ℂ) (q^(n+1)*x)
  norm_num only [norm_one] at hd
  linarith

theorem jacobi_factor_ne_zero {q x : ℂ} (hq : ‖q‖ < 1)
    (hx : ‖q‖*‖x‖ < 1) (n : ℕ) : 1-q^(n+1)*x ≠ 0 := by
  apply norm_pos_iff.mp
  exact (sub_pos.mpr hx).trans_le (jacobi_factor_denominator_bound hq x n)

theorem jacobi_log_term_norm_le {q x : ℂ} (hq : ‖q‖ < 1)
    (hx : ‖q‖*‖x‖ < 1) (n : ℕ) :
    ‖-q^(n+1)/(1-q^(n+1)*x)‖ ≤ ‖q‖^(n+1)/(1-‖q‖*‖x‖) := by
  rw [norm_div, norm_neg, norm_pow]
  exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg q) _)
    (sub_pos.mpr hx) (jacobi_factor_denominator_bound hq x n)

theorem jacobi_log_terms_summable {q x : ℂ} (hq : ‖q‖ < 1)
    (hx : ‖q‖*‖x‖ < 1) : Summable (fun n : ℕ => -q^(n+1)/(1-q^(n+1)*x)) := by
  have hs : Summable (fun n : ℕ => ‖q‖^(n+1)) := by
    simpa only [norm_mul, norm_pow, norm_one, mul_one] using
      jacobi_factor_norm_summable hq (1 : ℂ)
  exact Summable.of_norm_bounded (hs.div_const (1-‖q‖*‖x‖))
    (jacobi_log_term_norm_le hq hx)

theorem jacobi_factor_logDeriv (q x : ℂ) (n : ℕ) :
    logDeriv (fun y : ℂ => 1-q^(n+1)*y) x = -q^(n+1)/(1-q^(n+1)*x) := by
  have hd := ((hasDerivAt_id x).const_mul (q^(n+1))).const_sub 1
  simp only [id_eq, mul_one] at hd
  simp only [logDeriv, Pi.div_apply]
  rw [hd.deriv]

theorem jacobiFactorProduct_logDeriv {q x : ℂ} (hq : ‖q‖ < 1)
    (hx : ‖q‖*‖x‖ < 1) :
    logDeriv (jacobiFactorProduct q) x = ∑' n : ℕ, -q^(n+1)/(1-q^(n+1)*x) := by
  have hs : Summable (fun n : ℕ => logDeriv (fun y : ℂ => 1-q^(n+1)*y) x) := by
    simpa only [jacobi_factor_logDeriv] using jacobi_log_terms_summable hq hx
  have he := logDeriv_tprod_eq_tsum isOpen_univ (mem_univ x)
    (jacobi_factor_ne_zero hq hx) (fun n => by fun_prop) hs
    (jacobiFactorProduct_locally_uniform hq) (jacobiFactorProduct_ne_zero_of_norm hq hx)
  change logDeriv (fun y : ℂ => ∏' n : ℕ, (1-q^(n+1)*y)) x = _
  simpa only [jacobi_factor_logDeriv] using he

theorem jacobiFactorProduct_logDeriv_norm_le {q x : ℂ} (hq : ‖q‖ < 1)
    (hx : ‖q‖*‖x‖ < 1) :
    ‖logDeriv (jacobiFactorProduct q) x‖ ≤
      ‖q‖/((1-‖q‖)*(1-‖q‖*‖x‖)) := by
  have hs : Summable (fun n : ℕ => ‖q‖^(n+1)) := by
    simpa only [norm_mul, norm_pow, norm_one, mul_one] using
      jacobi_factor_norm_summable hq (1 : ℂ)
  have hn : Summable (fun n : ℕ => ‖-q^(n+1)/(1-q^(n+1)*x)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (jacobi_log_term_norm_le hq hx)
      (hs.div_const (1-‖q‖*‖x‖))
  rw [jacobiFactorProduct_logDeriv hq hx]
  calc
    _ ≤ ∑' n : ℕ, ‖-q^(n+1)/(1-q^(n+1)*x)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, ‖q‖^(n+1)/(1-‖q‖*‖x‖) :=
      Summable.tsum_le_tsum (jacobi_log_term_norm_le hq hx) hn (hs.div_const _)
    _ = _ := by
      rw [tsum_div_const]
      have he := jacobi_factor_norm_tsum hq (1 : ℂ)
      simp only [norm_pow, norm_one, mul_one] at he
      rw [he]
      exact div_div _ _ _

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiFactorProduct_logDeriv
#print axioms TwoAxisHelicoid.jacobiFactorProduct_logDeriv_norm_le
