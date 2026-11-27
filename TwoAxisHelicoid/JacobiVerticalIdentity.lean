import TwoAxisHelicoid.JacobiRealSeries
import TwoAxisHelicoid.EllipticFReciprocal

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] thetaG thetaEtaExpression jacobiRealE

theorem jacobiExp_imaginary_quotient (t a : ℝ) :
    jacobiExp (I*a/t) = (Real.exp (-Real.pi*a/t) : ℂ) := by
  unfold jacobiExp
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp only [I_sq]
  ring

theorem jacobi_vertical_region {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1) :
    jacobiExp (I*a/t) ≠ 1 ∧
      ‖jacobiNome (1/t)‖*‖jacobiExp (I*a/t)‖ < 1 ∧
      ‖jacobiNome (1/t)‖*‖(jacobiExp (I*a/t))⁻¹‖ < 1 := by
  have hrpos : 0 < Real.exp (-Real.pi*a/t) := Real.exp_pos _
  have hr : Real.exp (-Real.pi*a/t) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ha0) ht
  refine ⟨?_, ?_, ?_⟩
  · intro he
    rw [jacobiExp_imaginary_quotient] at he
    have h := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at h
    linarith
  · rw [jacobiNome_norm, jacobiExp_imaginary_quotient, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpos, ← Real.exp_add, Real.exp_lt_one_iff]
    rw [show -Real.pi*(1/t)+(-Real.pi*a/t) = -(Real.pi/t*(1+a)) by ring]
    exact neg_neg_of_pos (mul_pos (div_pos Real.pi_pos ht) (by linarith))
  · rw [jacobiNome_norm, norm_inv, jacobiExp_imaginary_quotient, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hrpos, ← div_eq_mul_inv, ← Real.exp_sub, Real.exp_lt_one_iff]
    rw [show -Real.pi*(1/t)-(-Real.pi*a/t) = -(Real.pi/t*(1-a)) by ring]
    exact neg_neg_of_pos (mul_pos (div_pos Real.pi_pos ht) (sub_pos.mpr ha1))

/-- Equation (7.3) of the manuscript, for the actual vertical period function.
Both the modular scaling and the infinite Jacobi series have been proved. -/
theorem thetaG_eq_jacobiRealE {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1) :
    thetaG t a = ((Real.pi^2/t^2)*
      jacobiRealE (-Real.exp (-Real.pi/t)) (Real.exp (-Real.pi*a/t)) : ℝ) := by
  have htinv := one_div_pos.mpr ht
  have haL : (a : ℂ) ∉ (rhombicPeriodPair t ht).lattice :=
    real_not_mem_rhombic_lattice_of_pos ht ha0 (by linarith)
  have he : (a : ℂ)/(I*t) = -(I*a/t) := by
    field_simp
    simp only [I_sq]
    ring
  have hz : (I*a/t : ℂ) ∉ (rhombicPeriodPair (1/t) htinv).lattice := by
    intro h
    apply reciprocal_not_mem_lattice ht haL
    rw [he]
    exact (rhombicPeriodPair (1/t) htinv).lattice.neg_mem h
  have hregion := jacobi_vertical_region ht ha0 ha1
  have hE := weierstrassP_add_eta_eq_jacobiSecondE htinv hz hregion.1 hregion.2.1 hregion.2.2
  rw [jacobiNome_eq_neg_exp, jacobiExp_imaginary_quotient,
    show -Real.pi*(1/t) = -Real.pi/t by ring, ← Complex.ofReal_neg,
    jacobiSecondE_ofReal] at hE
  rw [thetaG_eq_weierstrassP_of_pos ht ht a haL, rhombic_weierstrassP_reciprocal ht,
    thetaEtaExpression_reciprocal ht, he, PeriodPair.weierstrassP_neg]
  calc
    _ = -((rhombicPeriodPair (1/t) htinv).weierstrassP (I*a/t)+thetaEtaExpression (1/t))/(t : ℂ)^2 := by
      push_cast
      ring
    _ = _ := by
      rw [hE]
      push_cast
      ring

theorem thetaG_re_eq_jacobiRealE {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha1 : a < 1) :
    (thetaG t a).re = (Real.pi^2/t^2)*
      jacobiRealE (-Real.exp (-Real.pi/t)) (Real.exp (-Real.pi*a/t)) := by
  rw [thetaG_eq_jacobiRealE ht ha0 ha1, Complex.ofReal_re]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaG_eq_jacobiRealE
