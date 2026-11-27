import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace TwoAxisHelicoid
open ArithmeticFunction Finset

/-- Positive coefficients of the manuscript's half-period Fourier series,
expressed first by divisor sums at n and n/2. -/
noncomputable def halfPeriodPositiveCoefficient (n : ℕ) : ℝ :=
  if Even n then 4*(sigma 1 (n/2) : ℝ)-(sigma 1 n : ℝ) else (sigma 1 n : ℝ)

theorem sigma_one_two_power (k : ℕ) : (sigma 1 (2^k) : ℝ) = (2 : ℝ)^(k+1)-1 := by
  have hsum (j : ℕ) : (∑ i ∈ range j, (2 : ℝ)^i) = (2 : ℝ)^j-1 := by
    induction j with
    | zero => simp
    | succ j ih => rw [sum_range_succ,ih,pow_succ]; ring
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  push_cast
  exact hsum (k+1)

theorem sigma_one_two_power_odd (k : ℕ) {r : ℕ} (hr : Odd r) :
    (sigma 1 (2^k*r) : ℝ) = ((2 : ℝ)^(k+1)-1)*(sigma 1 r : ℝ) := by
  rw [isMultiplicative_sigma.map_mul_of_coprime (hr.coprime_two_left.pow_left k),
    Nat.cast_mul,sigma_one_two_power]

theorem halfPeriodPositiveCoefficient_odd {r : ℕ} (hr : Odd r) :
    halfPeriodPositiveCoefficient r = (sigma 1 r : ℝ) := by
  simp [halfPeriodPositiveCoefficient,Nat.not_even_iff_odd.mpr hr]

theorem halfPeriodPositiveCoefficient_two_power_succ (k : ℕ) {r : ℕ} (hr : Odd r) :
    halfPeriodPositiveCoefficient (2^(k+1)*r) =
      ((2 : ℝ)^(k+2)-3)*(sigma 1 r : ℝ) := by
  have he : Even (2^(k+1)*r) := ⟨2^k*r,by rw [pow_succ]; ring⟩
  have hh : 2^(k+1)*r/2 = 2^k*r := by
    calc 2^(k+1)*r/2 = ((2^k*r)*2)/2 := by rw [pow_succ]; congr 1; ring
         _ = 2^k*r := by omega
  rw [halfPeriodPositiveCoefficient,ite_eq_left he,hh,
    sigma_one_two_power_odd k hr,sigma_one_two_power_odd (k+1) hr]
  rw [show k+2 = (k+1)+1 by omega,pow_succ]
  ring

/-- The exact 2-adic coefficient formula appearing in the PDF. -/
theorem halfPeriodPositiveCoefficient_two_power (k : ℕ) {r : ℕ} (hr : Odd r) :
    halfPeriodPositiveCoefficient (2^k*r) =
      if k = 0 then (sigma 1 r : ℝ) else ((2 : ℝ)^(k+1)-3)*(sigma 1 r : ℝ) := by
  cases k with
  | zero => simpa using halfPeriodPositiveCoefficient_odd hr
  | succ k => simpa [Nat.succ_eq_add_one] using halfPeriodPositiveCoefficient_two_power_succ k hr

theorem halfPeriodPositiveCoefficient_bounds {n : ℕ} (hn : 0 < n) :
    1 ≤ halfPeriodPositiveCoefficient n ∧
      halfPeriodPositiveCoefficient n ≤ (sigma 1 n : ℝ) ∧ (sigma 1 n : ℝ) ≤ (n : ℝ)^2 := by
  have hs : (sigma 1 n : ℝ) ≤ (n : ℝ)^2 := by
    exact_mod_cast sigma_le_pow_succ 1 n
  have hb : 1 ≤ halfPeriodPositiveCoefficient n ∧
      halfPeriodPositiveCoefficient n ≤ (sigma 1 n : ℝ) := by
    obtain ⟨k,r,hr,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (ne_of_gt hn)
    have hrne : r ≠ 0 := by intro he; simp [he] at hr
    have hrp : (1 : ℝ) ≤ (sigma 1 r : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (sigma_pos 1 r hrne)
    cases k with
    | zero =>
      simpa only [pow_zero,one_mul,halfPeriodPositiveCoefficient_odd hr] using And.intro hrp le_rfl
    | succ k =>
      rw [halfPeriodPositiveCoefficient_two_power_succ k hr,sigma_one_two_power_odd (k+1) hr]
      have hpow : (4 : ℝ) ≤ (2 : ℝ)^(k+2) := by
        calc 4 = (2 : ℝ)^2 := by norm_num
             _ ≤ (2 : ℝ)^(k+2) := pow_le_pow_right₀ (by norm_num) (by omega)
      constructor <;> nlinarith
  exact ⟨hb.1,hb.2,hs⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.halfPeriodPositiveCoefficient_two_power
#print axioms TwoAxisHelicoid.halfPeriodPositiveCoefficient_bounds
