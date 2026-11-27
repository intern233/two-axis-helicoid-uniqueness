import TwoAxisHelicoid.ThetaScaledDerivative

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet

theorem sineJet_neg (j : ℕ) (v : ℂ) : sineJet j (-v) = (-1:ℂ)^(j+1)*sineJet j v := by
  induction j using Nat.twoStepInduction with
  | zero => simp [sineJet_zero]
  | one => simp [sineJet_one]
  | more j hj _ =>
    rw [sineJet_add_two,sineJet_add_two,hj]
    have hp : (-1:ℂ)^(j+2+1) = (-1:ℂ)^(j+1) := by
      rw [show j+2+1 = (j+1)+2 by omega,pow_add]
      norm_num
    rw [hp]
    ring

theorem thetaTerm_neg (t : ℝ) (j n : ℕ) (v : ℂ) :
    thetaTerm t j n (-v) = (-1:ℂ)^(j+1)*thetaTerm t j n v := by
  simp only [thetaTerm,mul_neg,sineJet_neg]
  ring

theorem thetaJet_neg (t : ℝ) (j : ℕ) (v : ℂ) :
    thetaJet t j (-v) = (-1:ℂ)^(j+1)*thetaJet t j v := by
  simp only [thetaJet,thetaTerm_neg,tsum_mul_left]

theorem thetaScaledJet_neg (t : ℝ) (j : ℕ) (z : ℂ) :
    thetaScaledJet t j (-z) = (-1:ℂ)^(j+1)*thetaScaledJet t j z := by
  simp only [thetaScaledJet,mul_neg,thetaJet_neg]
  ring

end TwoAxisHelicoid
