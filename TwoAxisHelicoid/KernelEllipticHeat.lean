import TwoAxisHelicoid.WeierstrassAddition
import TwoAxisHelicoid.WeightedPeriodContinuity

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaLt thetaLa thetaLz thetaP thetaLogSecond thetaLogThird thetaQuotient

noncomputable def thetaW (t : ℝ) (z : ℂ) : ℂ := thetaZeta t z-thetaEtaExpression t*z

theorem thetaW_quotient (t : ℝ) (z : ℂ) :
    thetaW t z = (Real.pi/2:ℂ)*thetaQuotient t 1 (Real.pi*z/2) := by
  rw [thetaW,thetaZeta_quotient,add_sub_cancel_right]

theorem thetaLa_elliptic_sum (t a : ℝ) (z : ℂ) :
    thetaLa t a z = -2*(thetaZeta t (z-a)-thetaZeta t z+thetaZeta t a) := by
  simp only [thetaZeta_quotient,thetaLa]
  ring

theorem thetaLa_elliptic_quotient {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice) (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice) (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaLa t a z = -((rhombicPeriodPair t ht).derivWeierstrassP z+
      (rhombicPeriodPair t ht).derivWeierstrassP a)/
        ((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a) := by
  rw [thetaLa_elliptic_sum,eq_div_iff (weierstrass_sub_ne_zero_of_sigma ht ha hz hm hp)]
  linear_combination -(thetaZeta_addition_cross ht ha hz hm hp)

theorem thetaLt_elliptic_raw {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice) (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice) :
    (Real.pi:ℂ)*thetaLt t a z = -2*thetaEtaExpression t+
      (rhombicPeriodPair t ht).weierstrassP a-(rhombicPeriodPair t ht).weierstrassP (z-a)+
      (rhombicPeriodPair t ht).weierstrassP z-thetaW t a^2+thetaW t (z-a)^2-thetaW t z^2-
      (a-1)*(rhombicPeriodPair t ht).derivWeierstrassP z-
      2*(a-1)*thetaW t z*((rhombicPeriodPair t ht).weierstrassP z+thetaEtaExpression t) := by
  rw [← thetaP_eq_weierstrassP ht ha,← thetaP_eq_weierstrassP ht hm,
    ← thetaP_eq_weierstrassP ht hz,← thetaLogThird_eq_weierstrassP_deriv ht hz]
  simp only [thetaW_quotient,thetaP,thetaLogSecond,thetaLogThird,thetaLt]
  rw [thetaEtaExpression_jet_ratio ht]
  ring

theorem thetaLt_elliptic_identity {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice) (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice) (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    (Real.pi:ℂ)*thetaLt t a z = thetaW t z*thetaLz t a z+thetaW t a*thetaLa t a z-
      (a-1)*(rhombicPeriodPair t ht).derivWeierstrassP z+
      2*(rhombicPeriodPair t ht).weierstrassP z+2*(rhombicPeriodPair t ht).weierstrassP a-
      2*thetaEtaExpression t := by
  have hadd : (thetaW t (z-a)-thetaW t z+thetaW t a)^2 =
      (rhombicPeriodPair t ht).weierstrassP (z-a)+(rhombicPeriodPair t ht).weierstrassP z+
        (rhombicPeriodPair t ht).weierstrassP a := by
    convert thetaZeta_weierstrass_addition ht ha hz hm hp using 1
    unfold thetaW
    ring
  have hsum := thetaLa_add_Lz_elliptic ht a hz
  have hLa : thetaLa t a z = -2*(thetaW t (z-a)-thetaW t z+thetaW t a) := by
    rw [thetaLa_elliptic_sum]
    unfold thetaW
    ring
  rw [thetaLt_elliptic_raw ht ha hz hm]
  rw [show thetaZeta t a = thetaW t a+thetaEtaExpression t*a by unfold thetaW; ring,hLa] at hsum
  rw [hLa]
  linear_combination hadd-thetaW t z*hsum

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaLa_elliptic_quotient
#print axioms TwoAxisHelicoid.thetaLt_elliptic_identity
