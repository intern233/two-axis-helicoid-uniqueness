import TwoAxisHelicoid.AllHeightPeriods
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace TwoAxisHelicoid
open Complex Set

noncomputable def heightBasisFlux (t : ℝ) (ht : 0 < t) (c : ℝ) (p : ℤ × ℤ) : ℝ :=
  ((p.1:ℂ)*heightPeriodTwo t ht c (Real.pi/t-(thetaEtaExpression t).re)+
    (p.2:ℂ)*heightPeriodHalf t ht c (Real.pi/t-(thetaEtaExpression t).re)).im

theorem heightPeriodHalf_closed_eq_I {t : ℝ} (ht : 0 < t) (c : ℝ) :
    heightPeriodHalf t ht c (Real.pi/t-(thetaEtaExpression t).re) =
      I*((-Real.pi*c/t:ℝ):ℂ) := by
  rw [heightPeriodHalf_closed_value_of_pos ht ht]
  push_cast
  ring

theorem heightPeriodTwo_closed_eq_I {t : ℝ} (ht : 0 < t) (c : ℝ) :
    heightPeriodTwo t ht c (Real.pi/t-(thetaEtaExpression t).re) =
      I*((-2*Real.pi*c/t:ℝ):ℂ) := by
  rw [heightPeriodTwo_closed_value_of_pos ht ht]
  push_cast
  ring

theorem heightPeriodHalf_closed_im_ne_zero {t c : ℝ} (ht : 0 < t) (hc : c ≠ 0) :
    (heightPeriodHalf t ht c (Real.pi/t-(thetaEtaExpression t).re)).im ≠ 0 := by
  rw [heightPeriodHalf_closed_eq_I ht c]
  simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,one_mul,zero_add]
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Real.pi_ne_zero) hc) ht.ne'

theorem heightBasisFlux_eq {t : ℝ} (ht : 0 < t) (c : ℝ) (p : ℤ × ℤ) :
    heightBasisFlux t ht c p = -Real.pi*c/t*(2*(p.1:ℝ)+(p.2:ℝ)) := by
  unfold heightBasisFlux
  rw [heightPeriodHalf_closed_eq_I ht c,heightPeriodTwo_closed_eq_I ht c]
  simp only [Complex.add_im,Complex.mul_im,Complex.mul_re,Complex.intCast_re,
    Complex.intCast_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,one_mul,zero_add,add_zero]
  ring

/-- Image of the integer combinations of the two explicitly integrated
primitive lattice generators. The surface-to-torus homology reduction is separate. -/
theorem heightBasisFlux_range {t : ℝ} (ht : 0 < t) (c : ℝ) :
    range (heightBasisFlux t ht c) = range (fun k : ℤ => (Real.pi*c/t)*(k:ℝ)) := by
  ext v
  constructor
  · rintro ⟨p,rfl⟩
    refine ⟨-(2*p.1+p.2),?_⟩
    rw [heightBasisFlux_eq]
    push_cast
    ring
  · rintro ⟨k,rfl⟩
    refine ⟨(0,-k),?_⟩
    rw [heightBasisFlux_eq]
    push_cast
    ring

theorem heightBasisFlux_minimum {t c : ℝ} (ht : 0 < t) (hc : c ≠ 0) :
    (∃ v ∈ range (heightBasisFlux t ht c), |v| = Real.pi*|c|/t ∧ v ≠ 0) ∧
      ∀ v ∈ range (heightBasisFlux t ht c), v ≠ 0 → Real.pi*|c|/t ≤ |v| := by
  rw [heightBasisFlux_range ht c]
  have hα : Real.pi*c/t ≠ 0 := div_ne_zero (mul_ne_zero Real.pi_ne_zero hc) ht.ne'
  have habs : |Real.pi*c/t| = Real.pi*|c|/t := by
    rw [abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos ht]
  constructor
  · refine ⟨Real.pi*c/t,⟨1,by simp⟩,habs,hα⟩
  · rintro v ⟨k,rfl⟩ hv
    have hk : k ≠ 0 := by intro h; simp [h] at hv
    have hkabs : (1:ℝ) ≤ |(k:ℝ)| := by
      have hpos : (0:ℤ) < |k| := abs_pos.mpr hk
      have hi : (1:ℤ) ≤ |k| := by omega
      exact_mod_cast hi
    rw [abs_mul,← habs]
    exact le_mul_of_one_le_right (abs_nonneg _) hkabs

theorem heightBasisFlux_normalized_minimum {t a c : ℝ} (ht : 0 < t)
    (ha : a < 1) (hc : |c| = 2*(1-a)) :
    (∃ v ∈ range (heightBasisFlux t ht c), |v| = 2*Real.pi*(1-a)/t ∧ v ≠ 0) ∧
      ∀ v ∈ range (heightBasisFlux t ht c), v ≠ 0 → 2*Real.pi*(1-a)/t ≤ |v| := by
  have hcn : c ≠ 0 := by intro h; simp only [h,abs_zero] at hc; linarith
  have h := heightBasisFlux_minimum ht hcn
  have he : Real.pi*|c|/t = 2*Real.pi*(1-a)/t := by rw [hc]; ring
  simpa only [he] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.heightBasisFlux_normalized_minimum
