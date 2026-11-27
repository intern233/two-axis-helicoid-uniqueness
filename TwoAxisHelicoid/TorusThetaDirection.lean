import TwoAxisHelicoid.CentralLevelThetaFactor
import TwoAxisHelicoid.SigmaQuasiPeriods

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
attribute [local irreducible] thetaScaledJet

/-- Removing the positive factor depending on the real coordinate leaves
a genuine torus-periodic representative of the corrected Gauss direction. -/
noncomputable def torusThetaDirection (t a : ℝ) (z : ℂ) : ℂ :=
  exp (I*((2*(1-a)*Real.pi/t*z.im:ℝ):ℂ))*
    (thetaScaledJet t 0 (z-a)/thetaScaledJet t 0 (z+a))

theorem theta_ratio_torus_direction (t a : ℝ) (z : ℂ) :
    centralPhaseThetaRatio t a z=
      (Real.exp (2*(1-a)*Real.pi/t*z.re):ℂ)*torusThetaDirection t a z := by
  let c := 2*(1-a)*Real.pi/t
  have e : (c:ℂ)*z=((c*z.re:ℝ):ℂ)+I*((c*z.im:ℝ):ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  unfold centralPhaseThetaRatio torusThetaDirection
  rw [← mul_assoc,ofReal_exp,← exp_add]
  exact congrArg (fun w : ℂ => exp w*_) e

private theorem direction_real_period (t a : ℝ) : Function.Periodic (torusThetaDirection t a) 2 := by
  intro z
  unfold torusThetaDirection
  rw [show z+2-(a:ℂ)=(z-a)+2 by ring,show z+2+(a:ℂ)=(z+a)+2 by ring,
    thetaScaledJet_zero_add_two,thetaScaledJet_zero_add_two]
  simp

private theorem direction_complex_period {t : ℝ} (ht : 0<t) (a : ℝ) :
    Function.Periodic (torusThetaDirection t a) (1+I*t) := by
  intro z
  let w : ℂ := 1+I*t
  let c := 2*(1-a)*Real.pi/t
  let A := fun u : ℂ => -Real.pi*I*(u+w/2)
  have phase : I*((c*t:ℝ):ℂ)+(A (z-a)-A (z+a))=2*Real.pi*I := by
    have ct : c*t=2*(1-a)*Real.pi := div_mul_cancel₀ _ ht.ne'
    rw [ct]
    dsimp [A]
    push_cast
    ring
  have yi : (z+w).im=z.im+t := by simp [w,Complex.mul_im]
  unfold torusThetaDirection
  change exp (I*((c*(z+w).im:ℝ):ℂ))*(_/_) = exp (I*((c*z.im:ℝ):ℂ))*(_/_)
  rw [show z+w-(a:ℂ)=(z-a)+w by ring,show z+w+(a:ℂ)=(z+a)+w by ring,
    thetaScaledJet_zero_add_half ht,thetaScaledJet_zero_add_half ht,thetaQuasiFactor_scaled,thetaQuasiFactor_scaled]
  have rat : (-exp (A (z-a))*thetaScaledJet t 0 (z-a))/(-exp (A (z+a))*thetaScaledJet t 0 (z+a)) =
      exp (A (z-a)-A (z+a))*(thetaScaledJet t 0 (z-a)/thetaScaledJet t 0 (z+a)) := by
    rw [exp_sub,mul_div_mul_comm]
    simp
  rw [rat,yi,mul_add,ofReal_add,mul_add,exp_add,← mul_assoc,
    mul_assoc (exp (I*↑(c*z.im))),← exp_add,phase,Complex.exp_two_pi_mul_I,mul_one]

theorem torusThetaDirection_add_lattice {t : ℝ} (ht : 0<t) (a : ℝ) (z : ℂ)
    {ω : ℂ} (member : ω∈(rhombicPeriodPair t ht).lattice) :
    torusThetaDirection t a (z+ω)=torusThetaDirection t a z := by
  obtain ⟨m,n,e⟩ := PeriodPair.mem_lattice.mp member
  rw [← e]
  change torusThetaDirection t a (z+((m:ℂ)*2+(n:ℂ)*(1+I*t)))=_
  have h₁ := (direction_real_period t a).zsmul m z
  have h₂ := (direction_complex_period ht a).zsmul n (z+(m:ℂ)*2)
  simp only [zsmul_eq_mul] at h₁ h₂
  rw [← add_assoc,h₂,h₁]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.theta_ratio_torus_direction
#print axioms TwoAxisHelicoid.torusThetaDirection_add_lattice
