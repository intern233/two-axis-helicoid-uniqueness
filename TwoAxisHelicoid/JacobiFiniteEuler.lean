import TwoAxisHelicoid.JacobiSecondLogDerivative
import TwoAxisHelicoid.JacobiFiniteProducts

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct

noncomputable def jacobiFiniteEuler (Q x : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, -Q^(n+1)*x/(1-Q^(n+1)*x)

theorem jacobi_power_region {Q x : ℂ} (hQ : ‖Q‖ < 1) (hx : ‖Q‖*‖x‖ < 1) (N : ℕ) :
    ‖Q‖*‖Q^N*x‖ < 1 := by
  have hn : ‖Q‖^N ≤ 1 := pow_le_one₀ (norm_nonneg Q) hQ.le
  rw [norm_mul, norm_pow]
  have h := mul_le_mul_of_nonneg_right hn (mul_nonneg (norm_nonneg Q) (norm_nonneg x))
  nlinarith

theorem jacobiEulerLog_split {Q x : ℂ} (hQ : ‖Q‖ < 1) (hx : ‖Q‖*‖x‖ < 1) (N : ℕ) :
    x*logDeriv (jacobiFactorProduct Q) x = jacobiFiniteEuler Q x N+
      (Q^N*x)*logDeriv (jacobiFactorProduct Q) (Q^N*x) := by
  have hs : Summable (fun n : ℕ => -Q^(n+1)*x/(1-Q^(n+1)*x)) := by
    convert (jacobi_log_terms_summable hQ hx).mul_right x using 1
    ext n
    ring
  have h := hs.sum_add_tsum_nat_add N
  have ht : (∑' n : ℕ, -Q^(n+N+1)*x/(1-Q^(n+N+1)*x)) =
      (Q^N*x)*logDeriv (jacobiFactorProduct Q) (Q^N*x) := by
    rw [jacobiEulerLog_eq_tsum hQ (jacobi_power_region hQ hx N)]
    apply tsum_congr
    intro n
    have he : Q^(n+N+1)*x = Q^(n+1)*(Q^N*x) := by
      rw [show n+N+1 = (n+1)+N by omega, pow_add]
      ring
    rw [show -Q^(n+N+1)*x = -(Q^(n+N+1)*x) by ring, he]
    ring
  rw [ht, ← jacobiEulerLog_eq_tsum hQ hx] at h
  exact h.symm

theorem jacobiEulerLog_tail_estimate {Q x : ℂ} (hQ : ‖Q‖ < 1)
    (hx : ‖Q‖*‖x‖ < 1) (N : ℕ) :
    ‖x*logDeriv (jacobiFactorProduct Q) x-jacobiFiniteEuler Q x N‖ ≤
      ‖Q^(N+1)*x‖/((1-‖Q‖)*(1-‖Q^(N+1)*x‖)) := by
  rw [jacobiEulerLog_split hQ hx N, add_sub_cancel_left, norm_mul]
  have h := mul_le_mul_of_nonneg_left
    (jacobiFactorProduct_logDeriv_norm_le hQ (jacobi_power_region hQ hx N)) (norm_nonneg (Q^N*x))
  have he : ‖Q‖*‖Q^N*x‖ = ‖Q^(N+1)*x‖ := by
    rw [← norm_mul]
    congr 1
    ring
  rw [he] at h
  calc
    _ ≤ ‖Q^N*x‖*(‖Q‖/((1-‖Q‖)*(1-‖Q^(N+1)*x‖))) := h
    _ = _ := by rw [← mul_div_assoc, mul_comm ‖Q^N*x‖ ‖Q‖, he]

theorem jacobiEulerLog_finite_error {Q x : ℂ} {N : ℕ} {σ τ : ℝ}
    (hσ : ‖Q‖ ≤ σ) (hσ1 : σ < 1) (hx : ‖Q‖*‖x‖ < 1)
    (hτ : ‖Q^(N+1)*x‖ ≤ τ) (hτ1 : τ < 1) :
    ‖x*logDeriv (jacobiFactorProduct Q) x-jacobiFiniteEuler Q x N‖ ≤
      τ/((1-σ)*(1-τ)) := by
  have hQ : ‖Q‖ < 1 := hσ.trans_lt hσ1
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans hτ
  have hd0 : 0 < (1-σ)*(1-τ) := mul_pos (sub_pos.mpr hσ1) (sub_pos.mpr hτ1)
  have hd : (1-σ)*(1-τ) ≤ (1-‖Q‖)*(1-‖Q^(N+1)*x‖) :=
    mul_le_mul (by linarith) (by linarith) (sub_pos.mpr hτ1).le (sub_pos.mpr hQ).le
  apply (jacobiEulerLog_tail_estimate hQ hx N).trans
  exact (div_le_div_of_nonneg_right hτ (hd0.trans_le hd).le).trans
    (div_le_div_of_nonneg_left hτ0 hd0 hd)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiEulerLog_finite_error
