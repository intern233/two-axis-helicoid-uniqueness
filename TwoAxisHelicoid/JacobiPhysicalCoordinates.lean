import TwoAxisHelicoid.DualProductIdentity
import TwoAxisHelicoid.HorizontalPeriodCentered

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct thetaA dualThetaA

noncomputable def physicalDualCoordinate (t : ℝ) (z : ℂ) : ℂ := 1/2-I*z/t
noncomputable def physicalJacobiX (t : ℝ) (z : ℂ) : ℂ := I*Complex.exp (Real.pi*z/t)

theorem physicalDualCoordinate_scale {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (I*t)*physicalDualCoordinate t z = z+I*((t/2 : ℝ) : ℂ) := by
  unfold physicalDualCoordinate
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  ring_nf
  simp only [I_sq]
  ring

theorem physicalJacobiX_eq (t : ℝ) (z : ℂ) :
    jacobiExp (physicalDualCoordinate t z) = physicalJacobiX t z := by
  unfold jacobiExp physicalDualCoordinate physicalJacobiX
  have he : I*(Real.pi : ℂ)*(1/2-I*z/t) = Real.pi/2*I+Real.pi*z/t := by
    ring_nf
    simp only [I_sq]
    ring
  rw [he, Complex.exp_add, Complex.exp_pi_div_two_mul_I]

theorem physicalJacobiX_ne_zero (t : ℝ) (z : ℂ) : physicalJacobiX t z ≠ 0 :=
  mul_ne_zero I_ne_zero (Complex.exp_ne_zero _)

theorem physicalJacobiX_inv (t : ℝ) (z : ℂ) :
    (physicalJacobiX t z)⁻¹ = -I*Complex.exp (-Real.pi*z/t) := by
  unfold physicalJacobiX
  rw [mul_inv_rev, Complex.inv_I]
  rw [show (-Real.pi*z/t : ℂ) = -(Real.pi*z/t) by ring, Complex.exp_neg]
  ring

theorem dual_nome_complex (t : ℝ) :
    jacobiNome (1/t) = -Complex.exp (-(Real.pi : ℂ)/t) := by
  rw [jacobiNome_eq_neg_exp]
  push_cast
  congr 2
  ring

theorem dual_r_complex (t a : ℝ) :
    (dualProductR t a : ℂ) = Complex.exp (-(Real.pi : ℂ)*a/t) := by
  unfold dualProductR
  push_cast
  rfl

theorem physical_qx (t : ℝ) (z : ℂ) :
    jacobiNome (1/t)*physicalJacobiX t z =
      -I*Complex.exp (Real.pi*(z-1)/t) := by
  rw [dual_nome_complex, physicalJacobiX]
  calc
    _ = -I*(Complex.exp (-(Real.pi : ℂ)/t)*Complex.exp (Real.pi*z/t)) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

theorem physical_qx_inv (t : ℝ) (z : ℂ) :
    jacobiNome (1/t)*(physicalJacobiX t z)⁻¹ =
      I*Complex.exp (-Real.pi*(z+1)/t) := by
  rw [dual_nome_complex, physicalJacobiX_inv]
  calc
    _ = I*(Complex.exp (-(Real.pi : ℂ)/t)*Complex.exp (-Real.pi*z/t)) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

theorem physical_rx (t a : ℝ) (z : ℂ) :
    (dualProductR t a : ℂ)*physicalJacobiX t z =
      I*Complex.exp (Real.pi*(z-a)/t) := by
  rw [dual_r_complex, physicalJacobiX]
  calc
    _ = I*(Complex.exp (-(Real.pi : ℂ)*a/t)*Complex.exp (Real.pi*z/t)) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

theorem physical_qrx (t a : ℝ) (z : ℂ) :
    jacobiNome (1/t)*((dualProductR t a : ℂ)*physicalJacobiX t z) =
      -I*Complex.exp (Real.pi*(z-a-1)/t) := by
  rw [dual_nome_complex, physical_rx]
  calc
    _ = -I*(Complex.exp (-(Real.pi : ℂ)/t)*Complex.exp (Real.pi*(z-a)/t)) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

theorem physical_qrx_inv (t a : ℝ) (z : ℂ) :
    jacobiNome (1/t)*((dualProductR t a : ℂ)*physicalJacobiX t z)⁻¹ =
      I*Complex.exp (Real.pi*(a-z-1)/t) := by
  rw [dual_nome_complex, physical_rx, mul_inv_rev, Complex.inv_I, ← Complex.exp_neg]
  calc
    _ = I*(Complex.exp (-(Real.pi : ℂ)/t)*Complex.exp (-(Real.pi*(z-a)/t))) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

theorem dual_q_div_r (t a : ℝ) :
    jacobiNome (1/t)/(dualProductR t a : ℂ) =
      -Complex.exp (-(dualProductKappa t a : ℂ)) := by
  rw [dual_nome_complex, dual_r_complex, neg_div, ← Complex.exp_sub]
  unfold dualProductKappa
  push_cast
  congr 2
  ring

theorem rhombic_open_horizontal_strip {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz0 : 0 < z.im) (hzt : z.im < t) : z ∉ (rhombicPeriodPair t ht).lattice := by
  intro hz
  obtain ⟨m,n,_,hi⟩ := (rhombic_mem_lattice_iff ht z).mp hz
  have hn0 : (0 : ℤ) < n := by
    exact_mod_cast (show (0 : ℝ) < n from (mul_pos_iff_of_pos_right ht).mp (hi ▸ hz0))
  have hn1 : n < (1 : ℤ) := by
    exact_mod_cast (show (n : ℝ) < 1 from (mul_lt_mul_iff_left₀ ht).mp (by simpa [mul_comm,hi] using hzt))
  omega

theorem shifted_horizontal_strip_not_mem {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : |z.im| < t/2) :
    z+I*((t/2 : ℝ) : ℂ) ∉ (rhombicPeriodPair t ht).lattice := by
  apply rhombic_open_horizontal_strip ht
  · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    linarith [(abs_lt.mp hz).1]
  · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    linarith [(abs_lt.mp hz).2]

theorem physicalDualCoordinate_not_mem_lattice {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z+I*((t/2 : ℝ) : ℂ) ∉ (rhombicPeriodPair t ht).lattice) : physicalDualCoordinate t z ∉
      (rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).lattice := by
  intro h
  have h' := (rhombic_reciprocal_mem_iff ht _).mp h
  rw [physicalDualCoordinate_scale ht] at h'
  exact hz h'

theorem physicalJacobiX_ne_one {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z+I*((t/2 : ℝ) : ℂ) ∉ (rhombicPeriodPair t ht).lattice) : physicalJacobiX t z ≠ 1 := by
  have hs := mt (thetaScaledJet_zero_iff_lattice_of_pos (one_div_pos.mpr ht)
    (one_div_pos.mpr ht) (physicalDualCoordinate t z)).mp
      (physicalDualCoordinate_not_mem_lattice ht hz)
  have hp := mul_ne_zero (jacobiTheta_normalization_ne_zero (one_div_pos.mpr ht)) hs
  rw [← rhombicProductTheta_eq_scaled_theta (one_div_pos.mpr ht)] at hp
  change jacobiThetaProduct (jacobiNome (1/t)) (physicalDualCoordinate t z) ≠ 0 at hp
  intro hx
  rw [jacobiThetaProduct_eq_pair, physicalJacobiX_eq, hx, sub_self, mul_zero, zero_mul] at hp
  exact hp rfl

theorem thetaA_eq_physical_product {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1)
    {z : ℂ} (hz : z+I*((t/2 : ℝ) : ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hp : ‖jacobiNome (1/t)‖*‖physicalJacobiX t z‖ < 1)
    (hm : ‖jacobiNome (1/t)‖*‖(physicalJacobiX t z)⁻¹‖ < 1) :
    thetaA t a (z+I*((t/2 : ℝ) : ℂ)) =
      dualProductIntegrand t a (physicalDualCoordinate t z) := by
  have hw := physicalDualCoordinate_not_mem_lattice ht hz
  have he := thetaA_reciprocal_theta ht
    (real_not_mem_rhombic_lattice_of_pos ht ha0 (by linarith)) hw
  rw [physicalDualCoordinate_scale ht] at he
  rw [he]
  apply dualThetaA_eq_product ht ha0 ha1
  · simpa only [physicalJacobiX_eq] using physicalJacobiX_ne_one ht hz
  · simpa only [physicalJacobiX_eq] using hp
  · simpa only [physicalJacobiX_eq] using hm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_eq_physical_product
