import TwoAxisHelicoid.SpinorMultipliers
import TwoAxisHelicoid.GaussDifferential
import TwoAxisHelicoid.SigmaAllPositive

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaSigma thetaZeta thetaGauss

theorem spinorExponent_neg_parameters (t a : ℝ) (m : ℤ) (z : ℂ) :
    spinorExponent t (-a) (-m) z = -spinorExponent t a m z := by
  unfold spinorExponent
  push_cast
  ring

theorem thetaSpinor_pair_product {t a : ℝ} (ht : 0 < t) (m : ℤ) {z : ℂ}
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaSpinor t a m z*thetaSpinor t (-a) (-m) z = thetaSigma t a^2*
      ((rhombicPeriodPair t ht).weierstrassP a-(rhombicPeriodPair t ht).weierstrassP z) := by
  have hσz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz
  have hσa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp ha
  have hAdd := thetaSigma_addition_of_pos ht ht ha hz
  unfold thetaSpinor
  rw [spinorExponent_neg_parameters,exp_neg,Complex.ofReal_neg,sub_neg_eq_add,← hAdd]
  field_simp [exp_ne_zero]

theorem thetaGauss_eq_spinor_ratio {t a : ℝ} (ht : 0 < t) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaGauss t a m z = I*thetaSpinor t a m z/thetaSpinor t (-a) (-m) z := by
  have hσz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz
  have hσp := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp
  have he : 2*((a : ℂ)-m)*thetaZeta t z+2*m*thetaEtaExpression t*z =
      spinorExponent t a m z+spinorExponent t a m z := by unfold spinorExponent; ring
  unfold thetaGauss thetaSpinor
  rw [spinorExponent_neg_parameters,exp_neg,Complex.ofReal_neg,sub_neg_eq_add,he,exp_add]
  field_simp [exp_ne_zero]

noncomputable def weierstrassSpinorOne (t a : ℝ) (m : ℤ) (C z : ℂ) : ℂ := C*thetaSpinor t a m z
noncomputable def weierstrassSpinorTwo (t a : ℝ) (m : ℤ) (C z : ℂ) : ℂ := -I*C*thetaSpinor t (-a) (-m) z

theorem weierstrassSpinor_product {t a c : ℝ} (ht : 0 < t) (m : ℤ) {C z : ℂ}
    (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    2*weierstrassSpinorOne t a m C z*weierstrassSpinorTwo t a m C z =
      I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a) := by
  have hσa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht a).mp ha
  unfold weierstrassSpinorOne weierstrassSpinorTwo
  calc
    _ = -2*I*C^2*(thetaSpinor t a m z*thetaSpinor t (-a) (-m) z) := by ring
    _ = _ := by
      rw [hC,thetaSpinor_pair_product ht m ha hz]
      field_simp
      ring

theorem weierstrassSpinor_gauss_relation {t a : ℝ} (ht : 0 < t) (m : ℤ) (C : ℂ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaGauss t a m z*weierstrassSpinorTwo t a m C z = weierstrassSpinorOne t a m C z := by
  have hsp : thetaSpinor t (-a) (-m) z ≠ 0 := by
    apply mt (thetaSpinor_zero_iff ht (-m) hz).mp
    simpa only [Complex.ofReal_neg,sub_neg_eq_add] using hp
  rw [thetaGauss_eq_spinor_ratio ht m hz hp]
  unfold weierstrassSpinorOne weierstrassSpinorTwo
  field_simp
  ring_nf
  simp [I_sq]

theorem weierstrassSpinor_square_one {t a c : ℝ} (ht : 0 < t) (m : ℤ) {C z : ℂ}
    (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    (weierstrassSpinorOne t a m C z)^2 = thetaGauss t a m z*
      (I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))/2 := by
  rw [← weierstrassSpinor_product ht m hC ha hz]
  have hg := weierstrassSpinor_gauss_relation ht m C hz hp
  linear_combination -(weierstrassSpinorOne t a m C z)*hg

theorem weierstrassSpinor_square_two {t a c : ℝ} (ht : 0 < t) (m : ℤ) {C z : ℂ}
    (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    (ha : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    (weierstrassSpinorTwo t a m C z)^2 =
      (I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))/
        (2*thetaGauss t a m z) := by
  have hg0 := thetaGauss_ne_zero ht a m hm hp
  rw [← weierstrassSpinor_product ht m hC ha hz]
  have hg := weierstrassSpinor_gauss_relation ht m C hz hp
  apply (eq_div_iff (mul_ne_zero (by norm_num) hg0)).mpr
  linear_combination 2*(weierstrassSpinorTwo t a m C z)*hg

theorem weierstrassSpinor_pair_not_both_zero {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C z : ℂ} (hC : C ≠ 0)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    weierstrassSpinorOne t a m C z ≠ 0 ∨ weierstrassSpinorTwo t a m C z ≠ 0 := by
  by_contra hn
  push Not at hn
  have hm : thetaSpinor t a m z = 0 := (mul_eq_zero.mp hn.1).resolve_left hC
  have hp : thetaSpinor t (-a) (-m) z = 0 :=
    (mul_eq_zero.mp hn.2).resolve_left (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hC)
  have hmL := (thetaSpinor_zero_iff ht m hz).mp hm
  have hpL := (thetaSpinor_zero_iff ht (-m) hz).mp hp
  have hL := (rhombicPeriodPair t ht).lattice.sub_mem hpL hmL
  have he : (z-((-a : ℝ) : ℂ))-(z-(a : ℂ)) = ((2*a : ℝ) : ℂ) := by push_cast; ring
  rw [he] at hL
  exact real_not_mem_rhombic_lattice_of_pos ht (by linarith [ha.1]) (by linarith [ha.2]) hL

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrassSpinor_square_one
#print axioms TwoAxisHelicoid.weierstrassSpinor_square_two
#print axioms TwoAxisHelicoid.weierstrassSpinor_pair_not_both_zero
