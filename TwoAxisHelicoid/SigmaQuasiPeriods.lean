import TwoAxisHelicoid.ThetaSigmaZeta

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet thetaScaledJet

theorem thetaScaledJet_zero_add_two (t : ℝ) (z : ℂ) :
    thetaScaledJet t 0 (z+2) = -thetaScaledJet t 0 z := by
  have harg : (Real.pi/2:ℂ)*(z+2) = (Real.pi/2:ℂ)*z+Real.pi := by ring
  simp only [thetaScaledJet,pow_zero,one_mul,harg,thetaJet_add_pi]

theorem thetaScaledJet_zero_add_half {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaScaledJet t 0 (z+(1+I*t)) =
      thetaQuasiFactor t (Real.pi*z/2)*thetaScaledJet t 0 z := by
  have harg : (Real.pi/2:ℂ)*(z+(1+I*t)) = Real.pi*z/2+thetaComplexHalfPeriod t := by
    unfold thetaComplexHalfPeriod
    ring
  have harg' : (Real.pi/2:ℂ)*z = Real.pi*z/2 := by ring
  simp only [thetaScaledJet,pow_zero,one_mul,harg,harg',thetaJet_zero_quasiperiod ht]

theorem thetaSigma_add_two (t : ℝ) (z : ℂ) :
    thetaSigma t (z+2) = -Complex.exp (2*thetaEtaExpression t*(z+1))*thetaSigma t z := by
  have he : Complex.exp (thetaEtaExpression t*(z+2)^2/2) =
      Complex.exp (2*thetaEtaExpression t*(z+1))*Complex.exp (thetaEtaExpression t*z^2/2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [thetaSigma,thetaScaledJet_zero_add_two,he]
  ring

theorem thetaQuasiFactor_scaled (t : ℝ) (z : ℂ) :
    thetaQuasiFactor t (Real.pi*z/2) = -Complex.exp (-Real.pi*I*(z+(1+I*t)/2)) := by
  have he : (Real.pi*I/2+Real.pi*t/2-2*(Real.pi*z/2)*I:ℂ) =
      -Real.pi*I*(z+(1+I*t)/2)+Real.pi*I := by
    ring_nf
    simp only [I_sq]
    ring
  unfold thetaQuasiFactor
  rw [he,Complex.exp_add,Complex.exp_pi_mul_I]
  ring

theorem thetaSigma_add_half {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaSigma t (z+(1+I*t)) =
      -Complex.exp ((thetaEtaExpression t*(1+I*t)-Real.pi*I)*(z+(1+I*t)/2))*thetaSigma t z := by
  have he : Complex.exp (thetaEtaExpression t*(z+(1+I*t))^2/2)*
      Complex.exp (-Real.pi*I*(z+(1+I*t)/2)) =
      Complex.exp ((thetaEtaExpression t*(1+I*t)-Real.pi*I)*(z+(1+I*t)/2))*
        Complex.exp (thetaEtaExpression t*z^2/2) := by
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    ring
  simp only [thetaSigma,thetaScaledJet_zero_add_half ht,thetaQuasiFactor_scaled]
  linear_combination (-thetaScaledJet t 0 z/thetaScaledJet t 1 0)*he

theorem thetaZeta_quotient (t : ℝ) (z : ℂ) :
    thetaZeta t z = (Real.pi/2:ℂ)*thetaQuotient t 1 (Real.pi*z/2)+thetaEtaExpression t*z := by
  have harg : (Real.pi/2:ℂ)*z = Real.pi*z/2 := by ring
  simp only [thetaZeta,thetaScaledJet,thetaQuotient,pow_zero,pow_one,one_mul,harg]
  ring

theorem thetaZeta_add_two (t : ℝ) (z : ℂ) :
    thetaZeta t (z+2) = thetaZeta t z+2*thetaEtaExpression t := by
  have harg : (Real.pi*(z+2)/2:ℂ) = Real.pi*z/2+Real.pi := by ring
  simp only [thetaZeta_quotient,harg,thetaQuotient_add_pi]
  ring

theorem thetaZeta_add_half {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    thetaZeta t (z+(1+I*t)) = thetaZeta t z+thetaEtaExpression t*(1+I*t)-Real.pi*I := by
  have hn : thetaJet t 0 (Real.pi*z/2) ≠ 0 := mt (thetaJet_zero_iff_rhombic_lattice ht z).mp hz
  have harg : (Real.pi*(z+(1+I*t))/2:ℂ) = Real.pi*z/2+thetaComplexHalfPeriod t := by
    unfold thetaComplexHalfPeriod
    ring
  simp only [thetaZeta_quotient,harg,thetaQuotient_one_quasiperiod ht0 hn]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigma_add_half
