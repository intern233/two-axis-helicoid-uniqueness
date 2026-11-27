import TwoAxisHelicoid.EllipticEtaHeat

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaScaledJet thetaSigma thetaZeta thetaLogSecond thetaP thetaEtaExpression

theorem thetaSigma_parameter_hasDerivAt_heat {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (fun s : ℝ => thetaSigma s z)
      (thetaSigma t z*(deriv thetaEtaExpression t*z^2/2+
        ((thetaZeta t z-thetaEtaExpression t*z)^2-
          (rhombicPeriodPair t ht).weierstrassP z+2*thetaEtaExpression t)/(2*(Real.pi:ℂ)))) t := by
  have ha := thetaScaledJet_one_ne_zero_of_pos ht
  have hz0 := mt (thetaScaledJet_zero_iff_lattice_of_pos ht ht z).mp hz
  have hη : HasDerivAt thetaEtaExpression (deriv thetaEtaExpression t) t :=
    (thetaEtaExpression_hasDerivAt_heat ht).differentiableAt.hasDerivAt
  have hE := ((hη.mul_const (z^2)).div_const 2).cexp
  have hd := (hE.mul (thetaScaledJet_parameter_hasDerivAt ht 0 z)).div
    (thetaScaledJet_parameter_hasDerivAt ht 1 0) ha
  convert hd using 1
  · funext s
    unfold thetaSigma
    rfl
  · have hP := thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hz
    rw [thetaLogSecond_scaled] at hP
    have hp : (rhombicPeriodPair t ht).weierstrassP z =
        (thetaScaledJet t 1 z/thetaScaledJet t 0 z)^2-
          thetaScaledJet t 2 z/thetaScaledJet t 0 z-thetaEtaExpression t := by
      linear_combination -hP
    rw [hp]
    simp only [Pi.mul_apply]
    unfold thetaSigma thetaZeta thetaEtaExpression
    norm_num only [Nat.reduceAdd]
    field_simp [ha,hz0,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigma_parameter_hasDerivAt_heat
