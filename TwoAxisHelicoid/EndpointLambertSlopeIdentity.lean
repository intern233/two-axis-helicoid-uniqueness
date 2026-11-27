import TwoAxisHelicoid.RightEndpointTheorem
import TwoAxisHelicoid.EtaLambertExpansion
import TwoAxisHelicoid.G2LambertExpansion

namespace TwoAxisHelicoid.VerticalAttachment

/-- The real expression at the end of the uploaded slope calculation. -/
noncomputable def endpointSlopeExpression (t η g₂ : ℝ) : ℝ :=
  let f := Real.pi/t
  let e := f-η
  let c := 6*e^2-g₂/2
  (f^2+2*e*f-(2/3)*c)/Real.pi

theorem endpointSlopeExpression_eq_actual {η g : ℝ}
    (hη : thetaEtaExpression ellipticVerticalUpper = (η : ℂ))
    (hg : (rhombicPeriodPair ellipticVerticalUpper ellipticVerticalUpper_pos).g₂ = (g : ℂ)) :
    endpointSlopeExpression ellipticVerticalUpper η g =
      derivWithin rightExtendedPeriod (Set.Iio ellipticVerticalUpper) ellipticVerticalUpper := by
  let T := ellipticVerticalUpper
  have ht : 0 < T := ellipticVerticalUpper_pos
  let L := rhombicPeriodPair T ht
  have hz : (1:ℂ) ∉ L.lattice :=
    real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  have hf : ellipticFReal T = Real.pi/T := by
    have eq := thetaG_one_eq_ellipticFReal ellipticVerticalUpper
    rw [thetaG_vertical_upper_one_zero, Complex.zero_re] at eq
    exact sub_eq_zero.mp eq.symm
  have hlog : thetaLogSecond T 1 = ((Real.pi/T : ℝ) : ℂ) := (thetaLogSecond_one_real T).trans (congrArg _ hf)
  have hw : L.weierstrassP 1 = ((Real.pi/T : ℝ) : ℂ) - (η : ℂ) := by
    have eq := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hz
    rw [hlog, hη] at eq
    exact eq_sub_of_add_eq eq.symm
  have fourth : thetaLogFourth T 1 = 6*(((Real.pi/T : ℝ) : ℂ)-η)^2-(g : ℂ)/2 := by
    rw [thetaLogFourth_eq_weierstrassP_second ht hz, rhombic_weierstrass_second_order ht hz, hw, hg]
  have eq : (Real.pi:ℂ)*rightSlopeTheta T = ((Real.pi*endpointSlopeExpression T η g : ℝ) : ℂ) := by
    rw [rightSlopeTheta_algebra ht, hlog, hη, fourth]
    unfold endpointSlopeExpression
    push_cast
    field_simp [Real.pi_ne_zero, ht.ne']
    ring
  have realEq := congrArg Complex.re eq
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at realEq
  rw [rightExtendedPeriod_hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio _),
    ← rightSlopeTheta_eq_period_slope ht]
  exact (mul_left_cancel₀ Real.pi_ne_zero realEq).symm

/-- The actual one-sided derivative is the endpoint expression with the two original infinite Lambert sums. -/
theorem endpoint_lambert_derivative :
    let t := ellipticVerticalUpper
    let q := -Real.exp (-Real.pi*t)
    let s₁ := ∑' n : ℕ, (n+1 : ℝ)*q^(n+1)/(1-q^(n+1))
    let s₃ := ∑' n : ℕ, (n+1 : ℝ)^3*q^(n+1)/(1-q^(n+1))
    endpointSlopeExpression t (Real.pi^2/12*(1-24*s₁)) (Real.pi^4/12*(1+240*s₃)) =
      derivWithin rightExtendedPeriod (Set.Iio t) t := by
  apply endpointSlopeExpression_eq_actual
  · rw [← thetaZeta_one]
    exact actual_eta_lambert_expansion ellipticVerticalUpper_pos
  · exact actual_g2_lambert_expansion ellipticVerticalUpper_pos

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.endpoint_lambert_derivative
