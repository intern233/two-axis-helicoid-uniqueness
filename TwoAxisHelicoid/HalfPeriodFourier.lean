import TwoAxisHelicoid.HalfPeriodLambert
import TwoAxisHelicoid.LambertDivisorSeries

namespace TwoAxisHelicoid
open ArithmeticFunction

theorem jacobi_plus_denominator_series {q : ℝ} (hq : |q| < 1) :
    (∑' n : ℕ, q^(n+1)/(1+q^(n+1))^2) =
      (∑' n : ℕ, (sigma 1 (n+1) : ℝ)*q^(n+1)) -
      4*(∑' n : ℕ, (sigma 1 (n+1) : ℝ)*(q^2)^(n+1)) := by
  have hq2 : |q^2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg q) hq (by decide : 2 ≠ 0)
  have hs (r : ℝ) (hr : |r| < 1) :
      Summable (fun n : ℕ => jacobiFraction (r^(n+1))) := by
    simpa only [pow_succ] using jacobiGeometricSeries_summable hr hr
  have he (n : ℕ) : q^(n+1)/(1+q^(n+1))^2 =
      jacobiFraction (q^(n+1))-4*jacobiFraction ((q^2)^(n+1)) := by
    have hp : |q^(n+1)| < 1 := by
      rw [abs_pow]
      exact pow_lt_one₀ (abs_nonneg q) hq (Nat.succ_ne_zero n)
    have h := jacobiFraction_pair hp
    rw [show (q^2)^(n+1) = (q^(n+1))^2 by ring]
    simp only [jacobiFraction, sub_neg_eq_add, neg_div] at h ⊢
    linear_combination -h
  rw [tsum_congr he, (hs q hq).tsum_sub ((hs (q^2) hq2).mul_left 4), tsum_mul_left]
  rw [jacobiFraction_series_eq_sigma (by simpa only [Real.norm_eq_abs] using hq),
    jacobiFraction_series_eq_sigma (by simpa only [Real.norm_eq_abs] using hq2)]

/-- A convergent divisor-sum Fourier expansion of the actual half-period
elliptic function. The separate power-of-two arithmetic identification with
the manuscript's positive coefficients is not asserted here. -/
theorem ellipticFReal_sigma_series {t : ℝ} (ht : 0 < t) :
    ellipticFReal t = Real.pi^2 * (1/4 +
      2*(∑' n : ℕ, (sigma 1 (n+1) : ℝ)*(-Real.exp (-Real.pi*t))^(n+1)) -
      8*(∑' n : ℕ, (sigma 1 (n+1) : ℝ)*((-Real.exp (-Real.pi*t))^2)^(n+1))) := by
  have hq : |-Real.exp (-Real.pi*t)| < 1 := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ht
  rw [ellipticFReal_lambert ht, jacobi_plus_denominator_series hq]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_sigma_series
