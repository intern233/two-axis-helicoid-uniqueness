import TwoAxisHelicoid.AxisCoefficientPositive
import TwoAxisHelicoid.WeierstrassCoordinateData
import TwoAxisHelicoid.WeierstrassAddition

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaGauss thetaZeta thetaEtaExpression

theorem thetaZeta_symmetric_difference {t : ℝ} (ht : 0 < t) {a z : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaZeta t (z-a)-thetaZeta t (z+a) = -2*thetaZeta t a+
      (rhombicPeriodPair t ht).derivWeierstrassP a/
        ((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a) := by
  have hden := weierstrass_sub_ne_zero_of_sigma ht ha hz hm hp
  have hminus := thetaZeta_addition_cross ht ha hz hm hp
  have hplus := thetaZeta_addition_cross ht
    (show -a ∉ (rhombicPeriodPair t ht).lattice by simpa using ha) hz
    (show z-(-a) ∉ (rhombicPeriodPair t ht).lattice by simpa using hp)
    (show z+(-a) ∉ (rhombicPeriodPair t ht).lattice by simpa only [sub_eq_add_neg] using hm)
  simp only [sub_neg_eq_add,← sub_eq_add_neg,thetaZeta_neg,
    (rhombicPeriodPair t ht).weierstrassP_neg,
    (rhombicPeriodPair t ht).derivWeierstrassP_neg] at hplus
  have he : (thetaZeta t (z-a)-thetaZeta t (z+a)+2*thetaZeta t a)*
      ((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a) =
      (rhombicPeriodPair t ht).derivWeierstrassP a := by
    linear_combination (hminus-hplus)/2
  have hd := (eq_div_iff hden).mpr he
  linear_combination hd

theorem thetaGaussLogDerivative_regular_part {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaGaussLogDerivative t a ht 1 z-
      2*(1-a)*((rhombicPeriodPair t ht).weierstrassP z-
        (rhombicPeriodPair t ht).weierstrassP a) = axisRegularCoefficient t ht a z := by
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have he := thetaZeta_symmetric_difference ht haL hz hm hp
  unfold thetaGaussLogDerivative axisRegularCoefficient
  norm_num only [Int.cast_one]
  linear_combination he

theorem actualGauss_end_regular_coefficient {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    deriv (thetaGauss t a 1) z/thetaGauss t a 1 z-
      I*((2*(a-1)/c : ℝ) : ℂ)*(coordinateData t a c ht z 2) =
      axisRegularCoefficient t ht a z := by
  rw [thetaGauss_log_derivative ht a 1 hz hm hp]
  have hi : I*((2*(a-1)/c : ℝ) : ℂ)*(coordinateData t a c ht z 2) =
      2*(1-a)*((rhombicPeriodPair t ht).weierstrassP z-
        (rhombicPeriodPair t ht).weierstrassP a) := by
    dsimp [coordinateData]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hc]
    ring_nf
    simp [I_sq,sub_eq_add_neg]
  rw [hi]
  exact thetaGaussLogDerivative_regular_part ht ha hz hm hp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualGauss_end_regular_coefficient
