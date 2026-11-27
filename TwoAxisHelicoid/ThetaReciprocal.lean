import TwoAxisHelicoid.ThetaAllZeroSet
import TwoAxisHelicoid.ThetaSimpleZeros

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet

theorem rhombicTau_gamma_den (t : ℝ) : 2*rhombicTau t-1 = I*t := by unfold rhombicTau; ring

theorem rhombicTau_gamma {t : ℝ} (ht : 0 < t) :
    (rhombicTau t-1)/(2*rhombicTau t-1) = rhombicTau (1/t) := by
  have hc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero hc
  rw [rhombicTau_gamma_den]
  unfold rhombicTau
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem rhombicTau_S_plus_two_ne_zero {t : ℝ} (ht : 0 < t) : -1/rhombicTau t+2 ≠ 0 := by
  have htau := rhombicTau_ne_zero ht
  intro h
  have he : 2*rhombicTau t-1 = 0 := by field_simp at h; linear_combination h
  rw [rhombicTau_gamma_den] at he
  exact (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')) he

noncomputable def thetaReciprocalFactor (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.pi*z/2)*I)*
    (jacobiOddInversionFactor (rhombicTau t) (z/2)*
      jacobiOddInversionFactor (-1/rhombicTau t+2) ((z/2)/rhombicTau t))*
        Complex.exp (-((Real.pi*(z/(I*t))/2)*I))

theorem thetaReciprocalFactor_ne_zero {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaReciprocalFactor t z ≠ 0 := by
  unfold thetaReciprocalFactor
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero
    (jacobiOddInversionFactor_ne_zero (rhombicTau_ne_zero ht) _)
    (jacobiOddInversionFactor_ne_zero (rhombicTau_S_plus_two_ne_zero ht) _))) (Complex.exp_ne_zero _)

theorem thetaReciprocalFactor_differentiable (t : ℝ) :
    Differentiable ℂ (thetaReciprocalFactor t) := by
  unfold thetaReciprocalFactor jacobiOddInversionFactor
  fun_prop

theorem thetaBilateral_scaled_eq_jacobiOdd {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (2*I)*thetaJet t 0 (Real.pi*z/2) =
      Complex.exp ((Real.pi*z/2)*I)*jacobiOdd (z/2) (rhombicTau t) := by
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (Real.pi*z/2)/Real.pi = z/2 := by field_simp
  simpa only [he] using thetaBilateral_eq_jacobiOdd ht (Real.pi*z/2)

theorem thetaJet_reciprocal {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaJet t 0 (Real.pi*z/2) = thetaReciprocalFactor t z*
      thetaJet (1/t) 0 (Real.pi*(z/(I*t))/2) := by
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
  have hg := jacobiOdd_gamma (z/2) (rhombicTau_ne_zero ht) (by rw [rhombicTau_gamma_den]; exact hi)
  rw [rhombicTau_gamma ht,rhombicTau_gamma_den] at hg
  have hz : (z/2)/(I*t) = (z/(I*t))/2 := by ring
  rw [hz] at hg
  have hnew := thetaBilateral_scaled_eq_jacobiOdd (one_div_pos.mpr ht) (z/(I*t))
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) I_ne_zero)
  calc
    (2*I)*thetaJet t 0 (Real.pi*z/2) =
      Complex.exp ((Real.pi*z/2)*I)*
        (jacobiOddInversionFactor (rhombicTau t) (z/2)*
          jacobiOddInversionFactor (-1/rhombicTau t+2) ((z/2)/rhombicTau t))*
            jacobiOdd ((z/(I*t))/2) (rhombicTau (1/t)) := by
      rw [thetaBilateral_scaled_eq_jacobiOdd ht,hg]
      ring
    _ = thetaReciprocalFactor t z*((2*I)*thetaJet (1/t) 0 (Real.pi*(z/(I*t))/2)) := by
      rw [hnew]
      unfold thetaReciprocalFactor
      rw [Complex.exp_neg]
      field_simp
    _ = (2*I)*(thetaReciprocalFactor t z*thetaJet (1/t) 0 (Real.pi*(z/(I*t))/2)) := by ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaJet_reciprocal
