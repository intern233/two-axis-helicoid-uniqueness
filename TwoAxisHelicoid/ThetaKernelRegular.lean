import TwoAxisHelicoid.SigmaAllPositive
import TwoAxisHelicoid.ThetaPeriodIntegral
import TwoAxisHelicoid.GaussDifferential

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaA thetaSigma thetaZeta

theorem thetaA_zero_iff_shift_lattice {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaA t a z = 0 ↔ z-a ∈ (rhombicPeriodPair t ht).lattice := by
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (a:ℂ)).mp ha
  have hsz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz
  rw [← thetaSigmaKernel_eq_thetaA_of_pos ht ht z ha hz]
  simp only [thetaSigmaKernel,mul_eq_zero,Complex.exp_ne_zero,false_or,
    div_eq_zero_iff,pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0),hsa,hsz,or_self,
    or_false,thetaSigma_zero_iff_lattice_of_pos ht ht]

theorem thetaA_neg_product {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (ha : (a:ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaA t a z*thetaA t a (-z) =
      ((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)^2 := by
  have hnz : -z ∉ (rhombicPeriodPair t ht).lattice := by simpa using hz
  have hsa := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (a:ℂ)).mp ha
  have hsz := mt (thetaSigma_zero_iff_lattice_of_pos ht ht z).mp hz
  rw [← thetaSigmaKernel_eq_thetaA_of_pos ht ht z ha hz,
    ← thetaSigmaKernel_eq_thetaA_of_pos ht ht (-z) ha hnz]
  have he : 2*(a-1)*thetaZeta t (-z)+2*thetaEtaExpression t*(-z) =
      -(2*(a-1)*thetaZeta t z+2*thetaEtaExpression t*z) := by
    rw [thetaZeta_neg]
    ring
  calc
    thetaSigmaKernel t a z*thetaSigmaKernel t a (-z) =
        (thetaSigma t (z-a)*thetaSigma t (z+a)/
          (thetaSigma t z^2*thetaSigma t (a:ℂ)^2))^2 := by
      unfold thetaSigmaKernel
      rw [he,Complex.exp_neg,show -z-(a:ℂ) = -(z+a) by ring,thetaSigma_neg,thetaSigma_neg]
      field_simp
    _ = ((rhombicPeriodPair t ht).weierstrassP a-(rhombicPeriodPair t ht).weierstrassP z)^2 := by
      rw [thetaSigma_addition_of_pos ht ht ha hz]
    _ = _ := by ring

theorem thetaA_pair_not_both_zero {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1)
    {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    thetaA t a z ≠ 0 ∨ thetaA t a (-z) ≠ 0 := by
  have haL := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have h2aL : (2:ℂ)*a ∉ (rhombicPeriodPair t ht).lattice := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      real_not_mem_rhombic_lattice_of_pos ht (show 0 < 2*a by linarith [ha.1])
        (show 2*a < 2 by linarith [ha.2])
  by_contra h
  push Not at h
  have hm := (thetaA_zero_iff_shift_lattice ht haL hz).mp h.1
  have hp := (thetaA_zero_iff_shift_lattice ht haL (show -z ∉ _ by simpa using hz)).mp h.2
  have hn := (rhombicPeriodPair t ht).lattice.neg_mem
    ((rhombicPeriodPair t ht).lattice.add_mem hm hp)
  apply h2aL
  convert hn using 1
  ring

theorem thetaA_analyticAt_off_lattice {t : ℝ} (ht : 0 < t) (a : ℝ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) : AnalyticAt ℂ (thetaA t a) z := by
  have hreg : z ∈ thetaRegular t := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht z).mp hz
  exact (thetaA_differentiableOn ht a).analyticAt ((thetaRegular_isOpen ht).mem_nhds hreg)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_pair_not_both_zero
