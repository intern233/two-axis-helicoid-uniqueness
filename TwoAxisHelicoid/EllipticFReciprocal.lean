import TwoAxisHelicoid.ZetaReciprocal
import TwoAxisHelicoid.ZetaHalfPeriod

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaZeta

theorem rhombic_reciprocal_one_add_half {t : ℝ} (ht : 0 < t) :
    (1:ℂ)/(I*t)+(1+I*((1/t:ℝ):ℂ)) = 1 := by
  have hc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero hc
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

theorem thetaEtaExpression_reciprocal {t : ℝ} (ht : 0 < t) :
    thetaEtaExpression t = (Real.pi/t:ℂ)-thetaEtaExpression (1/t)/(t:ℂ)^2 := by
  have htinv := one_div_pos.mpr ht
  have h1 : (1:ℂ) ∉ (rhombicPeriodPair t ht).lattice :=
    real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  have hs := thetaZeta_reciprocal ht h1
  rw [thetaZeta_one] at hs
  have hq := thetaZeta_add_half_of_pos htinv htinv (reciprocal_not_mem_lattice ht h1)
  rw [rhombic_reciprocal_one_add_half ht,thetaZeta_one] at hq
  have hv : thetaZeta (1/t) ((1:ℂ)/(I*t)) =
      Real.pi*I-thetaEtaExpression (1/t)*I*((1/t:ℝ):ℂ) := by linear_combination -hq
  rw [hs,hv]
  have hc : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hi : (I*t:ℂ) ≠ 0 := mul_ne_zero I_ne_zero hc
  push_cast
  field_simp

theorem rhombic_weierstrassP_one_reciprocal {t : ℝ} (ht : 0 < t) :
    (rhombicPeriodPair t ht).weierstrassP 1 =
      -(rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).weierstrassP 1/(t:ℂ)^2 := by
  let L := rhombicPeriodPair (1/t) (one_div_pos.mpr ht)
  have hp := L.weierstrassP_add_coe ((1:ℂ)/(I*t)) ⟨L.ω₂,L.ω₂_mem_lattice⟩
  change L.weierstrassP (1/(I*t)+(1+I*((1/t:ℝ):ℂ))) = L.weierstrassP (1/(I*t)) at hp
  rw [rhombic_reciprocal_one_add_half ht] at hp
  rw [rhombic_weierstrassP_reciprocal ht 1]
  change -(1/(t:ℂ)^2)*L.weierstrassP (1/(I*t)) = -L.weierstrassP 1/(t:ℂ)^2
  rw [← hp]
  ring

noncomputable def ellipticF (t : ℝ) (ht : 0 < t) : ℝ :=
  (thetaEtaExpression t+(rhombicPeriodPair t ht).weierstrassP 1).re

theorem ellipticF_reciprocal {t : ℝ} (ht : 0 < t) :
    ellipticF t ht = Real.pi/t-ellipticF (1/t) (one_div_pos.mpr ht)/t^2 := by
  have he : thetaEtaExpression t+(rhombicPeriodPair t ht).weierstrassP 1 =
      (Real.pi/t:ℂ)-(thetaEtaExpression (1/t)+
        (rhombicPeriodPair (1/t) (one_div_pos.mpr ht)).weierstrassP 1)/(t:ℂ)^2 := by
    rw [thetaEtaExpression_reciprocal ht,rhombic_weierstrassP_one_reciprocal ht]
    ring
  unfold ellipticF
  rw [he,← Complex.ofReal_pow]
  simp only [Complex.sub_re,Complex.div_ofReal_re,Complex.ofReal_re]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticF_reciprocal
