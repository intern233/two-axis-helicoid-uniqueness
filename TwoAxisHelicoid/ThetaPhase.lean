import TwoAxisHelicoid.ThetaBasic
import Mathlib.Data.Nat.Periodic

namespace TwoAxisHelicoid

noncomputable def thetaPhase (n : ℂ) : ℂ := Complex.exp (Real.pi*Complex.I*n*(n-1)/2)

theorem thetaPhase_nat_periodic : Function.Periodic (fun n : ℕ => thetaPhase n) 4 := by
  intro n
  unfold thetaPhase
  dsimp only
  have he : (Real.pi*Complex.I*(n+4 : ℕ)*((n+4 : ℕ)-1)/2 : ℂ) =
      Real.pi*Complex.I*n*(n-1)/2+((2*n+3 : ℕ) : ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow, mul_one]

theorem thetaPhase_nat (n : ℕ) : thetaPhase n = thetaSign n := by
  rw [← thetaPhase_nat_periodic.map_mod_nat n]
  have hn : n%4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : n%4 <;> simp only [thetaSign, h] <;> norm_num [thetaPhase]
  all_goals
    have he : (Real.pi*Complex.I*3 : ℂ) = Real.pi*Complex.I+2*Real.pi*Complex.I := by ring
    rw [he, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I, mul_one]

theorem thetaPhase_neg_sub_one (n : ℂ) : thetaPhase (-n-1) = -thetaPhase n * Complex.exp (2*Real.pi*Complex.I*n) := by
  unfold thetaPhase
  have he : (Real.pi*Complex.I*(-n-1)*((-n-1)-1)/2 : ℂ) =
      Real.pi*Complex.I*n*(n-1)/2+Real.pi*Complex.I+2*Real.pi*Complex.I*n := by ring
  rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem thetaPhase_int_neg_sub_one (n : ℤ) : thetaPhase (-n-1) = -thetaPhase n := by
  rw [thetaPhase_neg_sub_one]
  have he : (2*Real.pi*Complex.I*n : ℂ) = (n : ℂ)*(2*Real.pi*Complex.I) := by ring
  rw [he, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaPhase_nat
