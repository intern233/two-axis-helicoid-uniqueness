import TwoAxisHelicoid.RectanglePrimitive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace TwoAxisHelicoid
open Complex Real Set MeasureTheory
open scoped Interval

noncomputable def rectangleBoundary (f : ℂ → ℂ) (a b : ℝ) : ℂ :=
  (∫ x : ℝ in -a..a, f ((x : ℂ)-(b : ℂ)*I))-
  (∫ x : ℝ in -a..a, f ((x : ℂ)+(b : ℂ)*I))+
  I*(∫ y : ℝ in -b..b, f ((a : ℂ)+(y : ℂ)*I))-
  I*(∫ y : ℝ in -b..b, f (-(a : ℂ)+(y : ℂ)*I))

theorem inverse_horizontal_continuous (b : ℝ) (hb : b ≠ 0) :
    Continuous (fun x : ℝ => ((x : ℂ)+(b : ℂ)*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro x hx
  have hi := congrArg Complex.im hx
  exact hb (by simpa using hi)

theorem inverse_vertical_continuous (a : ℝ) (ha : a ≠ 0) :
    Continuous (fun y : ℝ => ((a : ℂ)+(y : ℂ)*I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro y hy
  have hr := congrArg Complex.re hy
  exact ha (by simpa using hr)

theorem inverse_horizontal_pair (x b : ℝ) :
    ((x : ℂ)-(b : ℂ)*I)⁻¹-((x : ℂ)+(b : ℂ)*I)⁻¹ =
      2*I*((b/(b^2+x^2) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    norm_num only [Complex.inv_re,Complex.inv_im,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,
      mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,sub_zero,zero_sub] <;> ring

theorem inverse_vertical_pair (a y : ℝ) :
    ((a : ℂ)+(y : ℂ)*I)⁻¹-(-(a : ℂ)+(y : ℂ)*I)⁻¹ =
      2*((a/(a^2+y^2) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    norm_num only [Complex.inv_re,Complex.inv_im,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat,
      mul_zero,zero_mul,zero_add,add_zero,mul_one,one_mul,sub_zero,zero_sub] <;> ring

/-- The residue contribution of a single simple pole, computed on a rectangle
using real arctangent integrals. No winding or residue theorem is assumed. -/
theorem rectangleBoundary_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    rectangleBoundary (fun z : ℂ => z⁻¹) a b = 2*Real.pi*I := by
  have hbottom : IntervalIntegrable (fun x : ℝ => ((x : ℂ)-(b : ℂ)*I)⁻¹) volume (-a) a := by
    simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
      (inverse_horizontal_continuous (-b) (neg_ne_zero.mpr hb.ne')).intervalIntegrable (μ := volume) (-a) a
  have htop := (inverse_horizontal_continuous b hb.ne').intervalIntegrable (μ := volume) (-a) a
  have hright := (inverse_vertical_continuous a ha.ne').intervalIntegrable (μ := volume) (-b) b
  have hleft := (inverse_vertical_continuous (-a) (neg_ne_zero.mpr ha.ne')).intervalIntegrable (μ := volume) (-b) b
  have he : rectangleBoundary (fun z : ℂ => z⁻¹) a b =
      (∫ x : ℝ in -a..a, 2*I*((b/(b^2+x^2) : ℝ) : ℂ))+
        I*(∫ y : ℝ in -b..b, 2*((a/(a^2+y^2) : ℝ) : ℂ)) := by
    simp_rw [← inverse_horizontal_pair,← inverse_vertical_pair]
    rw [intervalIntegral.integral_sub hbottom htop,
      intervalIntegral.integral_sub hright (by simpa only [Complex.ofReal_neg] using hleft)]
    unfold rectangleBoundary
    ring
  rw [he,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal,
    integral_div_sq_add_sq,integral_div_sq_add_sq]
  rw [neg_div,neg_div,arctan_neg,arctan_neg]
  have hat : arctan (a/b)+arctan (b/a) = Real.pi/2 := by
    have h := arctan_inv_of_pos (div_pos ha hb)
    rw [inv_div] at h
    linarith
  have hatc := congrArg (fun x : ℝ => (x : ℂ)) hat
  push_cast at hatc ⊢
  linear_combination 4*I*hatc

theorem rectangleBoundary_holomorphic_zero {f : ℂ → ℂ} {a b l r d u : ℝ}
    (hf : DifferentiableOn ℂ f (complexOpenRect l r d u))
    (hbottom : -(a : ℂ)-(b : ℂ)*I ∈ complexOpenRect l r d u)
    (htop : (a : ℂ)+(b : ℂ)*I ∈ complexOpenRect l r d u) :
    rectangleBoundary f a b = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (-(a : ℂ)-(b : ℂ)*I) ((a : ℂ)+(b : ℂ)*I)
    (hf.mono (rectangle_subset_openRect hbottom htop))
  simpa [rectangleBoundary,Complex.mul_re,Complex.mul_im,smul_eq_mul,sub_eq_add_neg] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rectangleBoundary_inv
