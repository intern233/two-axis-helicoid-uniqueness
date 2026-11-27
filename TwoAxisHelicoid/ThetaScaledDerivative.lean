import TwoAxisHelicoid.ThetaSimpleZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaJet

noncomputable def thetaScaledJet (t : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  (Real.pi/2:ℂ)^j*thetaJet t j ((Real.pi/2:ℂ)*z)

noncomputable def thetaLogSecond (t : ℝ) (z : ℂ) : ℂ :=
  (Real.pi^2/4:ℂ)*(thetaQuotient t 1 (Real.pi*z/2)^2-thetaQuotient t 2 (Real.pi*z/2))

noncomputable def thetaEtaExpression (t : ℝ) : ℂ :=
  -thetaScaledJet t 3 0/(3*thetaScaledJet t 1 0)

theorem thetaScaledJet_hasDerivAt {t : ℝ} (ht : 0 < t) (j : ℕ) (z : ℂ) :
    HasDerivAt (thetaScaledJet t j) (thetaScaledJet t (j+1) z) z := by
  have hd := ((thetaJet_hasDerivAt ht j ((Real.pi/2:ℂ)*z)).comp z
    ((hasDerivAt_id z).const_mul (Real.pi/2:ℂ))).const_mul ((Real.pi/2:ℂ)^j)
  convert hd using 1
  · rfl
  · simp only [thetaScaledJet,pow_succ,mul_one]
    ring

theorem thetaScaledJet_analyticAt {t : ℝ} (ht : 0 < t) (j : ℕ) (z : ℂ) :
    AnalyticAt ℂ (thetaScaledJet t j) z :=
  (show Differentiable ℂ (thetaScaledJet t j) from
    fun w => (thetaScaledJet_hasDerivAt ht j w).differentiableAt).analyticAt z

theorem thetaScaledJet_iteratedDeriv {t : ℝ} (ht : 0 < t) (j n : ℕ) :
    iteratedDeriv n (thetaScaledJet t j) = thetaScaledJet t (j+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext z
    simpa only [Nat.add_assoc] using (thetaScaledJet_hasDerivAt ht (j+n) z).deriv

theorem thetaLogSecond_scaled (t : ℝ) (z : ℂ) :
    thetaLogSecond t z = (thetaScaledJet t 1 z/thetaScaledJet t 0 z)^2-
      thetaScaledJet t 2 z/thetaScaledJet t 0 z := by
  have hz : (Real.pi/2:ℂ)*z = Real.pi*z/2 := by ring
  simp only [thetaLogSecond,thetaScaledJet,pow_zero,one_mul,pow_one,hz,thetaQuotient]
  ring

theorem thetaScaledJet_zero_at_zero (t : ℝ) : thetaScaledJet t 0 0 = 0 := by
  simp only [thetaScaledJet,pow_zero,mul_zero,thetaJet_zero_at_zero]

theorem thetaScaledJet_one_ne_zero {t : ℝ} (ht : 43/50 ≤ t) : thetaScaledJet t 1 0 ≠ 0 := by
  simp only [thetaScaledJet,pow_one,mul_zero]
  exact mul_ne_zero (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by norm_num))
    (thetaJet_one_at_zero_ne_zero ht)

theorem thetaScaledJet_two_at_zero (t : ℝ) : thetaScaledJet t 2 0 = 0 := by
  have hz : thetaJet t 2 0 = 0 := by
    have hterm (n : ℕ) : thetaTerm t 2 n 0 = 0 := by simp [thetaTerm,sineJet]
    simp only [thetaJet,hterm,tsum_zero]
  simp only [thetaScaledJet,mul_zero,hz]

theorem thetaLogSecond_eq_zero_of_theta_zero {t : ℝ} {z : ℂ}
    (hz : thetaJet t 0 (Real.pi*z/2) = 0) : thetaLogSecond t z = 0 := by
  simp only [thetaLogSecond,thetaQuotient,hz,div_zero,zero_pow (by decide : 2 ≠ 0),
    sub_zero,mul_zero]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaLogSecond_scaled
