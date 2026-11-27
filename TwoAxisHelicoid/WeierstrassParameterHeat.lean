import TwoAxisHelicoid.EllipticEtaHeat

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaP thetaLogSecond thetaLogThird thetaLogFourth thetaJet

theorem thetaP_hasDerivAt_heat {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (fun s : ℝ => thetaP s z)
      ((2*(rhombicPeriodPair t ht).weierstrassP z^2-
        2*thetaEtaExpression t*(rhombicPeriodPair t ht).weierstrassP z-
        (rhombicPeriodPair t ht).g₂/3+
        (thetaZeta t z-thetaEtaExpression t*z)*(rhombicPeriodPair t ht).derivWeierstrassP z)/
        (Real.pi:ℂ)) t := by
  have hn := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mp hz
  have hd := (thetaLogSecond_parameter_hasDerivAt ht hn).sub (thetaEtaExpression_hasDerivAt_heat ht)
  convert hd using 1
  · funext s
    simp only [thetaP,Pi.sub_apply]
  · rw [thetaLogFourth_eq_weierstrassP_second ht hz,rhombic_weierstrass_second_order ht hz,
      thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hz,thetaLogThird_eq_weierstrassP_deriv ht hz]
    ring

noncomputable def actualWeierstrassPFamily (t : ℝ) (z : ℂ) : ℂ :=
  if ht : 0 < t then (rhombicPeriodPair t ht).weierstrassP z else 0

theorem actualWeierstrassPFamily_hasDerivAt_heat {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (fun s : ℝ => actualWeierstrassPFamily s z)
      ((2*(rhombicPeriodPair t ht).weierstrassP z^2-
        2*thetaEtaExpression t*(rhombicPeriodPair t ht).weierstrassP z-
        (rhombicPeriodPair t ht).g₂/3+
        (thetaZeta t z-thetaEtaExpression t*z)*(rhombicPeriodPair t ht).derivWeierstrassP z)/
        (Real.pi:ℂ)) t := by
  apply (thetaP_hasDerivAt_heat ht hz).congr_of_eventuallyEq
  have hn := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mp hz
  have hcont := (thetaJet_parameter_hasDerivAt ht 0 (Real.pi*z/2)).continuousAt
  filter_upwards [eventually_gt_nhds ht,hcont.eventually_ne hn] with s hs hn
  rw [actualWeierstrassPFamily,dite_eq_left hs]
  exact (thetaP_eq_weierstrassP hs (mt (thetaJet_zero_iff_rhombic_lattice_of_pos hs z).mpr hn)).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualWeierstrassPFamily_hasDerivAt_heat
