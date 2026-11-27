import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Arithmetic bounds for the coefficient formula (5.6)

The function below is the explicit divisor-sum expression for an index
`n = 2 ^ k * r`. The bounds do not require `r` to be odd. This file proves
arithmetic facts about the expression; it does not prove that the Fourier
series of the Weierstrass functions has these coefficients.
-/

namespace TwoAxisHelicoid

def fourierCoefficient (k r : ℕ) : ℕ :=
  if k = 0 then ArithmeticFunction.sigma 1 r
  else (2 ^ (k + 1) - 3) * ArithmeticFunction.sigma 1 r

/-- The factor in the even-index case is positive. -/
theorem fourier_factor_pos {k : ℕ} (hk : 0 < k) :
    1 ≤ 2 ^ (k + 1) - 3 := by
  have hpow : (2 : ℕ) ^ 2 ≤ 2 ^ (k + 1) :=
    pow_le_pow_right' (by norm_num) (by omega)
  norm_num at hpow
  omega

/-- The factor grows more slowly than the square of the power-of-two part. -/
theorem fourier_factor_le_square (k : ℕ) :
    2 ^ (k + 1) - 3 ≤ (2 ^ k) ^ 2 := by
  by_cases hk : k = 0
  · subst k
    norm_num
  · have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ k :=
      pow_le_pow_right' (by norm_num) (by omega)
    norm_num at hpow
    calc
      2 ^ (k + 1) - 3 ≤ 2 ^ (k + 1) := Nat.sub_le _ _
      _ = (2 ^ k) * 2 := pow_succ _ _
      _ ≤ (2 ^ k) * (2 ^ k) := Nat.mul_le_mul_left _ hpow
      _ = (2 ^ k) ^ 2 := (pow_two _).symm

/-- The first bound in (5.6): every coefficient for a positive odd part
is at least one. Oddness is not needed for this bound. -/
theorem fourier_coefficient_one_le (k : ℕ) {r : ℕ} (hr : 0 < r) :
    1 ≤ fourierCoefficient k r := by
  have hs : 1 ≤ ArithmeticFunction.sigma 1 r :=
    ArithmeticFunction.sigma_pos 1 r (Nat.ne_zero_of_lt hr)
  unfold fourierCoefficient
  split_ifs with hk
  · exact hs
  · simpa using Nat.mul_le_mul (fourier_factor_pos (Nat.pos_of_ne_zero hk)) hs

/-- The quadratic bound used in (5.8). -/
theorem fourier_coefficient_le_square (k r : ℕ) :
    fourierCoefficient k r ≤ (2 ^ k * r) ^ 2 := by
  have hs : ArithmeticFunction.sigma 1 r ≤ r ^ 2 :=
    ArithmeticFunction.sigma_le_pow_succ 1 r
  unfold fourierCoefficient
  split_ifs with hk
  · subst k
    simpa using hs
  · calc
      (2 ^ (k + 1) - 3) * ArithmeticFunction.sigma 1 r
          ≤ (2 ^ k) ^ 2 * r ^ 2 :=
        Nat.mul_le_mul (fourier_factor_le_square k) hs
      _ = (2 ^ k * r) ^ 2 := (mul_pow _ _ _).symm

theorem fourier_coefficient_bounds (k : ℕ) {r : ℕ} (hr : 0 < r) :
    1 ≤ fourierCoefficient k r ∧ fourierCoefficient k r ≤ (2 ^ k * r) ^ 2 :=
  ⟨fourier_coefficient_one_le k hr, fourier_coefficient_le_square k r⟩

/-- The index-dependent coefficient, using the actual power of two dividing `n`. -/
def fourierCoefficientAt (n : ℕ) : ℕ :=
  fourierCoefficient (n.factorization 2) (n / 2 ^ n.factorization 2)

theorem fourier_index_decomposition (n : ℕ) :
    2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
  Nat.ordProj_mul_ordCompl_eq_self n 2

theorem fourier_odd_part_not_two_dvd {n : ℕ} (hn : 0 < n) :
    ¬ 2 ∣ n / 2 ^ n.factorization 2 :=
  Nat.not_dvd_ordCompl Nat.prime_two (Nat.ne_zero_of_lt hn)

/-- The full-index coefficient bound for every positive integer, as used
to dominate the tail of the Fourier series. -/
theorem fourier_coefficient_at_bounds {n : ℕ} (hn : 0 < n) :
    1 ≤ fourierCoefficientAt n ∧ fourierCoefficientAt n ≤ n ^ 2 := by
  have hr : 0 < n / 2 ^ n.factorization 2 :=
    Nat.ordCompl_pos 2 (Nat.ne_zero_of_lt hn)
  obtain ⟨hlo, hhi⟩ := fourier_coefficient_bounds (n.factorization 2) hr
  rw [fourier_index_decomposition] at hhi
  exact ⟨hlo, hhi⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.fourier_factor_pos
#print axioms TwoAxisHelicoid.fourier_factor_le_square
#print axioms TwoAxisHelicoid.fourier_coefficient_one_le
#print axioms TwoAxisHelicoid.fourier_coefficient_le_square
#print axioms TwoAxisHelicoid.fourier_coefficient_bounds
#print axioms TwoAxisHelicoid.fourier_coefficient_at_bounds
