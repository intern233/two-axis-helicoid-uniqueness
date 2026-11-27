import TwoAxisHelicoid.ThetaBilateral
import TwoAxisHelicoid.JacobiOddModular

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet

noncomputable def rhombicTau (t : ℝ) : ℂ := (1+I*t)/2

theorem thetaBilateralTerm_eq_jacobi (t : ℝ) (n : ℤ) (v : ℂ) :
    thetaBilateralTerm t n v = Complex.exp (v*I)*
      jacobiTheta₂_term n (v/Real.pi+(rhombicTau t-1)/2) (rhombicTau t) := by
  unfold thetaBilateralTerm thetaPhase jacobiTheta₂_term rhombicTau
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem thetaBilateral_eq_jacobiOdd {t : ℝ} (ht : 0 < t) (v : ℂ) :
    (2*I)*thetaJet t 0 v = Complex.exp (v*I)*jacobiOdd (v/Real.pi) (rhombicTau t) := by
  rw [← thetaBilateral_sum ht]
  simp_rw [thetaBilateralTerm_eq_jacobi,tsum_mul_left]
  change Complex.exp (v*I)*jacobiTheta₂ (v/Real.pi+(rhombicTau t-1)/2) (rhombicTau t) = _
  have he : (v/Real.pi+(rhombicTau t-1)/2)+1 = v/Real.pi+(rhombicTau t+1)/2 := by ring
  rw [← jacobiTheta₂_add_left (v/Real.pi+(rhombicTau t-1)/2),he]
  rfl

theorem thetaJet_zero_iff_jacobiOdd {t : ℝ} (ht : 0 < t) (v : ℂ) :
    thetaJet t 0 v = 0 ↔ jacobiOdd (v/Real.pi) (rhombicTau t) = 0 := by
  have h := congrArg (fun w : ℂ => w=0) (thetaBilateral_eq_jacobiOdd ht v)
  simpa only [mul_eq_zero,mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) I_ne_zero,
    Complex.exp_ne_zero,false_or] using Iff.of_eq h

theorem thetaJet_scaled_zero_iff_jacobiOdd {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaJet t 0 (Real.pi*z/2) = 0 ↔ jacobiOdd (z/2) (rhombicTau t) = 0 := by
  rw [thetaJet_zero_iff_jacobiOdd ht]
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (Real.pi*z/2)/Real.pi = z/2 := by field_simp
  rw [he]

theorem rhombicTau_ne_zero {t : ℝ} (ht : 0 < t) : rhombicTau t ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [rhombicTau,Complex.mul_im] at hi
  linarith

theorem thetaJet_scaled_zero_iff_reciprocal {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaJet t 0 (Real.pi*z/2) = 0 ↔
      thetaJet (1/t) 0 (Real.pi*(z/(I*t))/2) = 0 := by
  have hc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero hc
  have hd : 2*rhombicTau t-1 = I*t := by unfold rhombicTau; ring
  have hgamma : (rhombicTau t-1)/(2*rhombicTau t-1) = rhombicTau (1/t) := by
    rw [hd]
    unfold rhombicTau
    push_cast
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  rw [thetaJet_scaled_zero_iff_jacobiOdd ht,thetaJet_scaled_zero_iff_jacobiOdd (one_div_pos.mpr ht)]
  rw [jacobiOdd_zero_iff_gamma _ (rhombicTau_ne_zero ht) (by rw [hd]; exact hi),hgamma,hd]
  have hz : (z/2)/(I*t) = (z/(I*t))/2 := by ring
  rw [hz]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaJet_scaled_zero_iff_reciprocal
