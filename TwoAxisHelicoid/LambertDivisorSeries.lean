import TwoAxisHelicoid.JacobiRealSeries
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

namespace TwoAxisHelicoid
open ArithmeticFunction

theorem jacobiFraction_pow_eq_pnat_sum {q : ℝ} (hq : ‖q‖ < 1) (d : ℕ+) :
    jacobiFraction (q^(d : ℕ)) =
      ∑' c : ℕ+, (c : ℝ) * q^((d : ℕ)*(c : ℕ)) := by
  have hp : ‖q^(d : ℕ)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq d.ne_zero
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one hp
  have he := tsum_zero_pnat_eq_tsum_nat hs.summable
  simp only [Nat.cast_zero, zero_mul, zero_add] at he
  rw [jacobiFraction, ← hs.tsum_eq, ← he]
  apply tsum_congr
  intro c
  rw [pow_mul]

/-- Absolute summability justifies the rearrangement by divisors; this is
the precise bridge from squared geometric denominators to sigma_1. -/
theorem jacobiFraction_series_eq_sigma {q : ℝ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, jacobiFraction (q^(n+1))) =
      ∑' n : ℕ, (sigma 1 (n+1) : ℝ) * q^(n+1) := by
  have h := tsum_prod_pow_eq_tsum_sigma 1 hq
  simp only [pow_one, ← jacobiFraction_pow_eq_pnat_sum hq] at h
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => jacobiFraction (q^n)),
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (sigma 1 n : ℝ)*q^n)] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiFraction_series_eq_sigma
