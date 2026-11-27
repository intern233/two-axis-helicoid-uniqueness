import TwoAxisHelicoid.SigmaAllIdentities
import TwoAxisHelicoid.ZetaHalfPeriod

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate
attribute [local irreducible] thetaSigma thetaZeta thetaGauss

noncomputable def thetaGaussLogDerivative (t a : ℝ) (ht : 0 < t) (m : ℤ) (z : ℂ) : ℂ :=
  2*(m-a)*(rhombicPeriodPair t ht).weierstrassP z+2*m*thetaEtaExpression t+
    thetaZeta t (z-a)-thetaZeta t (z+a)

theorem thetaGauss_ne_zero {t : ℝ} (ht : 0 < t) (a : ℝ) (m : ℤ) {z : ℂ}
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) : thetaGauss t a m z ≠ 0 := by
  unfold thetaGauss
  exact div_ne_zero (mul_ne_zero (mul_ne_zero I_ne_zero (Complex.exp_ne_zero _))
    (mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z-a)).mp hm))
      (mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp)

theorem thetaGauss_hasDerivAt {t : ℝ} (ht : 0 < t) (a : ℝ) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (thetaGauss t a m) (thetaGauss t a m z*thetaGaussLogDerivative t a ht m z) z := by
  have hsm := (thetaSigma_hasDerivAt_zeta_of_pos ht ht hm).comp (h := fun w : ℂ => w-a) z
    ((hasDerivAt_id z).sub_const (a:ℂ))
  have hsp := (thetaSigma_hasDerivAt_zeta_of_pos ht ht hp).comp (h := fun w : ℂ => w+a) z
    ((hasDerivAt_id z).add_const (a:ℂ))
  have he := (((thetaZeta_hasDerivAt_of_pos ht ht hz).const_mul (2*((a:ℂ)-(m:ℂ)))).add
    ((hasDerivAt_id z).const_mul (2*(m:ℂ)*thetaEtaExpression t))).cexp
  have hd := (((he.const_mul I).mul hsm).div hsp
    (mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp))
  convert hd using 1
  · unfold thetaGauss
    rfl
  · simp only [Function.comp_apply,Pi.mul_apply,Pi.add_apply,id_eq,mul_one]
    unfold thetaGauss thetaGaussLogDerivative
    have hn := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp
    field_simp
    ring

theorem thetaGauss_log_derivative {t : ℝ} (ht : 0 < t) (a : ℝ) (m : ℤ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    deriv (thetaGauss t a m) z/thetaGauss t a m z = thetaGaussLogDerivative t a ht m z := by
  rw [(thetaGauss_hasDerivAt ht a m hz hm hp).deriv]
  exact mul_div_cancel_left₀ _ (thetaGauss_ne_zero ht a m hm hp)

theorem thetaSigma_conj (t : ℝ) (z : ℂ) : thetaSigma t (conj z) = conj (thetaSigma t z) := by
  unfold thetaSigma
  simp only [map_div₀,map_mul,← Complex.exp_conj,map_pow,thetaScaledJet_conj,
    thetaEtaExpression_conj,map_ofNat]
  have h0 := thetaScaledJet_conj t 1 0
  simp only [map_zero] at h0
  rw [← h0]

theorem thetaZeta_conj (t : ℝ) (z : ℂ) : thetaZeta t (conj z) = conj (thetaZeta t z) := by
  unfold thetaZeta
  simp only [map_add,map_div₀,map_mul,thetaScaledJet_conj,thetaEtaExpression_conj]

theorem thetaGauss_conj (t a : ℝ) (m : ℤ) (z : ℂ) :
    thetaGauss t a m (conj z) = -conj (thetaGauss t a m z) := by
  have hm : conj z-a = conj (z-a) := by simp
  have hp : conj z+a = conj (z+a) := by simp
  unfold thetaGauss
  rw [hm,hp,thetaSigma_conj,thetaSigma_conj,thetaZeta_conj]
  simp only [map_div₀,map_mul,← Complex.exp_conj,map_add,map_sub,map_intCast,
    map_ofNat,Complex.conj_ofReal,Complex.conj_I,thetaEtaExpression_conj]
  ring

theorem thetaGauss_neg_product {t : ℝ} (ht : 0 < t) (a : ℝ) (m : ℤ) {z : ℂ}
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaGauss t a m (-z)*thetaGauss t a m z = -1 := by
  have hsm := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z-a)).mp hm
  have hsp := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp
  have hmz : -z-a = -(z+a) := by ring
  have hpz : -z+a = -(z-a) := by ring
  have he : 2*(a-m)*thetaZeta t (-z)+2*m*thetaEtaExpression t*(-z) =
      -(2*(a-m)*thetaZeta t z+2*m*thetaEtaExpression t*z) := by rw [thetaZeta_neg]; ring
  unfold thetaGauss
  rw [he,Complex.exp_neg,hmz,hpz,thetaSigma_neg,thetaSigma_neg]
  field_simp
  norm_num [I_sq]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaGauss_log_derivative
#print axioms TwoAxisHelicoid.thetaGauss_conj
#print axioms TwoAxisHelicoid.thetaGauss_neg_product
