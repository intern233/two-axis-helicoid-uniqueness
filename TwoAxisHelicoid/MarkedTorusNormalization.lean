import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace TwoAxisHelicoid
open Complex

/-- Algebraic periods of `(A ℘ + B) dz` in a marking with first period one.
The complete quasi-periods are `η₁, ητ`, not half-period values. -/
noncomputable def markedHeightPeriods (τ η₁ ητ A B : ℂ) : ℂ × ℂ :=
  (B-A*η₁,B*τ-A*ητ)

theorem marked_height_period_relation (τ η₁ ητ A B : ℂ)
    (hLegendre : η₁*τ-ητ = 2*Real.pi*I) :
    (markedHeightPeriods τ η₁ ητ A B).2 =
      (markedHeightPeriods τ η₁ ητ A B).1*τ+2*Real.pi*I*A := by
  dsimp [markedHeightPeriods]
  linear_combination A*hLegendre

/-- The explicit normalization formula in Appendix C.1 for arbitrary complex
principal coefficient and arbitrary upper-half-plane marking. Identifying
these algebraic periods with a differential is a separate analytic step. -/
theorem marked_real_period_normalization {τ η₁ ητ A B : ℂ}
    (hτ : 0 < τ.im) (hLegendre : η₁*τ-ητ = 2*Real.pi*I) :
    ((markedHeightPeriods τ η₁ ητ A B).1.re = 0 ∧
      (markedHeightPeriods τ η₁ ητ A B).2.re = 0) ↔
      B = A*η₁-2*Real.pi*I*((A.im/τ.im : ℝ) : ℂ) := by
  rw [marked_height_period_relation τ η₁ ητ A B hLegendre]
  change ((B-A*η₁).re = 0 ∧ ((B-A*η₁)*τ+2*Real.pi*I*A).re = 0) ↔ _
  constructor
  · rintro ⟨h₁,h₂⟩
    have he : (B-A*η₁).im = -2*Real.pi*A.im/τ.im := by
      apply (eq_div_iff hτ.ne').mpr
      simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,
        h₁,zero_mul,mul_zero,mul_one,sub_zero,add_zero,zero_sub] at h₂
      linarith
    apply Complex.ext
    · simpa only [Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,
        zero_mul,mul_zero,mul_one,sub_zero,zero_add,add_zero,zero_sub] using sub_eq_zero.mp h₁
    · simp only [Complex.sub_im,Complex.mul_im] at he
      simp only [Complex.sub_im,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,
        zero_mul,mul_zero,mul_one,sub_zero,zero_add,add_zero]
      linear_combination he
  · rintro rfl
    constructor <;>
      simp only [sub_sub_cancel_left,Complex.neg_re,Complex.neg_im,Complex.add_re,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,
        zero_mul,mul_zero,mul_one,sub_zero,zero_add,add_zero,zero_sub,neg_zero]
    field_simp
    ring

theorem marked_height_nonzero_imaginary_period {τ η₁ ητ A B : ℂ}
    (hLegendre : η₁*τ-ητ = 2*Real.pi*I) (hA : A ≠ 0)
    (hclosed : (markedHeightPeriods τ η₁ ητ A B).1.re = 0 ∧
      (markedHeightPeriods τ η₁ ητ A B).2.re = 0) :
    (markedHeightPeriods τ η₁ ητ A B).1.im ≠ 0 ∨
      (markedHeightPeriods τ η₁ ητ A B).2.im ≠ 0 := by
  by_contra hn
  simp only [not_or,not_not] at hn
  have h₁ : (markedHeightPeriods τ η₁ ητ A B).1 = 0 :=
    Complex.ext hclosed.1 hn.1
  have h₂ : (markedHeightPeriods τ η₁ ητ A B).2 = 0 :=
    Complex.ext hclosed.2 hn.2
  have he := marked_height_period_relation τ η₁ ητ A B hLegendre
  rw [h₁,h₂,zero_mul,zero_add] at he
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) hA) he.symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.marked_real_period_normalization
#print axioms TwoAxisHelicoid.marked_height_nonzero_imaginary_period
