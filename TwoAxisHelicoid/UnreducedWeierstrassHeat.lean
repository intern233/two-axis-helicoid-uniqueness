import TwoAxisHelicoid.WeierstrassParameterHeat
import TwoAxisHelicoid.EllipticParameterAnalytic

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology
attribute [local irreducible] thetaLogSecond thetaLogThird thetaLogFourth thetaEtaExpression thetaJet

/-- The intermediate heat equation in Appendix A.1 before substitution for
the derivative of η. Here η is differentiated as an analytic function of the
real modulus. Its numerical derivative formula is not used. -/
theorem actualWeierstrassPFamily_unreduced_heat {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    let L := rhombicPeriodPair t ht
    (Real.pi : ℂ) * deriv (fun s : ℝ => actualWeierstrassPFamily s z) t =
      2*(L.weierstrassP z)^2 - 2*thetaEtaExpression t*L.weierstrassP z -
      (thetaEtaExpression t)^2 - L.g₂/4 +
      (thetaZeta t z-thetaEtaExpression t*z)*L.derivWeierstrassP z -
      (Real.pi : ℂ)*deriv thetaEtaExpression t := by
  dsimp only
  have hn := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mp hz
  have cont := (thetaJet_parameter_hasDerivAt ht 0 (Real.pi*z/2)).continuousAt
  have same : (fun s : ℝ => actualWeierstrassPFamily s z) =ᶠ[𝓝 t]
      (fun s : ℝ => thetaLogSecond s z) - thetaEtaExpression := by
    filter_upwards [eventually_gt_nhds ht,cont.eventually_ne hn] with s hs hn'
    have regular := mt (thetaJet_zero_iff_rhombic_lattice_of_pos hs z).mpr hn'
    simp only [actualWeierstrassPFamily,dite_eq_left hs,Pi.sub_apply]
    rw [thetaLogSecond_eq_weierstrassP_add_eta_of_pos hs hs regular]
    ring
  have hd := (thetaLogSecond_parameter_hasDerivAt ht hn).sub
    (thetaEtaExpression_analyticAt ht).differentiableAt.hasDerivAt
  rw [same.deriv_eq,hd.deriv,thetaLogFourth_eq_weierstrassP_second ht hz,
    rhombic_weierstrass_second_order ht hz,thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hz,
    thetaLogThird_eq_weierstrassP_deriv ht hz]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualWeierstrassPFamily_unreduced_heat
