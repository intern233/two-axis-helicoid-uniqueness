import TwoAxisHelicoid.WeierstrassLogGauss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Complex Set

noncomputable def endHorizontalSupport (θ : ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  Real.sin θ • ContinuousLinearMap.proj 0-Real.cos θ • ContinuousLinearMap.proj 1

@[simp] theorem endHorizontalSupport_apply (θ : ℝ) (v : Fin 3 → ℝ) :
    endHorizontalSupport θ v = Real.sin θ*v 0-Real.cos θ*v 1 := rfl

theorem endHorizontalSupport_bound (θ : ℝ) {v : Fin 3 → ℝ} {B : ℝ}
    (h0 : |v 0| ≤ B) (h1 : |v 1| ≤ B) :
    |endHorizontalSupport θ v| ≤ 2*B := by
  rw [endHorizontalSupport_apply]
  calc |Real.sin θ*v 0-Real.cos θ*v 1| ≤ |Real.sin θ*v 0|+|Real.cos θ*v 1| := abs_sub _ _
       _ ≤ 1*B+1*B := by
         rw [abs_mul,abs_mul]
         exact add_le_add
           (mul_le_mul (Real.abs_sin_le_one θ) h0 (abs_nonneg _) (by norm_num))
           (mul_le_mul (Real.abs_cos_le_one θ) h1 (abs_nonneg _) (by norm_num))
       _ = 2*B := by ring

theorem endHorizontalSupport_tangent (θ u v : ℝ) :
    endHorizontalSupport θ (logGaussTangentY u v) = Real.cosh u*Real.cos (v-θ) := by
  simp only [endHorizontalSupport_apply,logGaussTangentY,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Real.cos_sub]
  ring

theorem endHorizontalSupport_tangent_lower {θ u v : ℝ} (hphase : |v-θ| ≤ 1) :
    1/2 ≤ endHorizontalSupport θ (logGaussTangentY u v) := by
  rw [endHorizontalSupport_tangent]
  have hs : (v-θ)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hphase
  have hcos : (1 : ℝ)/2 ≤ Real.cos (v-θ) := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v-θ)]
  calc (1 : ℝ)/2 ≤ Real.cos (v-θ) := hcos
       _ ≤ Real.cosh u*Real.cos (v-θ) := by
         simpa using mul_le_mul_of_nonneg_right (Real.one_le_cosh u)
           (show 0 ≤ Real.cos (v-θ) by linarith)

theorem height_end_support_hasDerivAt {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α x y : ℝ)
    (hX : HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y))) 1))
        ((x : ℂ)+I*y)) :
    HasDerivAt (fun s : ℝ => endHorizontalSupport (α*x) (X ((x : ℂ)+I*s)))
      (Real.cosh (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y)).re *
        Real.cos (F ((x : ℂ)+I*y)).im) y := by
  have hγ : HasDerivAt (fun s : ℝ => (x : ℂ)+I*s) I y := by
    have hr : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 y := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := y))
    simpa using (hr.const_mul I).const_add (x : ℂ)
  have hd := ((endHorizontalSupport (α*x)).hasFDerivAt.comp _ hX).comp_hasDerivAt y hγ
  have he := (weierstrass_exp_real_tangents (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y))).2
  have hi : (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y)).im-α*x = (F ((x : ℂ)+I*y)).im := by
    simp [Complex.mul_im,Complex.mul_re]
  simpa only [ContinuousLinearMap.comp_apply,he,endHorizontalSupport_tangent,hi,Function.comp_def] using hd

/-- A small correction to the helicoidal logarithmic Gauss map forces a
uniformly positive horizontal support derivative along vertical height
coordinate lines. This gives spatial escape, not just intrinsic length. -/
theorem height_end_support_deriv_lower {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α x y : ℝ)
    (hX : HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y))) 1))
        ((x : ℂ)+I*y))
    (hF : |(F ((x : ℂ)+I*y)).im| ≤ 1) :
    1/2 ≤ deriv (fun s : ℝ => endHorizontalSupport (α*x) (X ((x : ℂ)+I*s))) y := by
  rw [(height_end_support_hasDerivAt α x y hX).deriv]
  have hs : (F ((x : ℂ)+I*y)).im^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hF
  have hcos : (1 : ℝ)/2 ≤ Real.cos (F ((x : ℂ)+I*y)).im := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := (F ((x : ℂ)+I*y)).im)]
  calc (1 : ℝ)/2 ≤ Real.cos (F ((x : ℂ)+I*y)).im := hcos
       _ ≤ _ := by
         simpa using mul_le_mul_of_nonneg_right
           (Real.one_le_cosh (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y)).re)
           (show 0 ≤ Real.cos (F ((x : ℂ)+I*y)).im by linarith)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_end_support_deriv_lower
