import TwoAxisHelicoid.HeightEndGrowth
import TwoAxisHelicoid.DerivativeCone

namespace TwoAxisHelicoid
open Complex Set

noncomputable def endHorizontalTransverse (θ : ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  Real.cos θ • ContinuousLinearMap.proj 0+Real.sin θ • ContinuousLinearMap.proj 1

@[simp] theorem endHorizontalTransverse_apply (θ : ℝ) (v : Fin 3 → ℝ) :
    endHorizontalTransverse θ v = Real.cos θ*v 0+Real.sin θ*v 1 := rfl

theorem endHorizontalTransverse_tangent (θ u v : ℝ) :
    endHorizontalTransverse θ (logGaussTangentY u v) = Real.cosh u*Real.sin (v-θ) := by
  simp only [endHorizontalTransverse_apply,logGaussTangentY,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Real.sin_sub]
  ring

theorem height_end_transverse_hasDerivAt {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α x y : ℝ)
    (hX : HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y))) 1))
        ((x : ℂ)+I*y)) :
    HasDerivAt (fun s : ℝ => endHorizontalTransverse (α*x) (X ((x : ℂ)+I*s)))
      (Real.cosh (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y)).re *
        Real.sin (F ((x : ℂ)+I*y)).im) y := by
  have hγ : HasDerivAt (fun s : ℝ => (x : ℂ)+I*s) I y := by
    have hr : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 y := by
      simpa using! (Complex.ofRealCLM.hasDerivAt (x := y))
    simpa using (hr.const_mul I).const_add (x : ℂ)
  have hd := ((endHorizontalTransverse (α*x)).hasFDerivAt.comp _ hX).comp_hasDerivAt y hγ
  have he := (weierstrass_exp_real_tangents (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y))).2
  have hi : (I*α*((x : ℂ)+I*y)+F ((x : ℂ)+I*y)).im-α*x = (F ((x : ℂ)+I*y)).im := by
    simp [Complex.mul_im,Complex.mul_re]
  simpa only [ContinuousLinearMap.comp_apply,he,endHorizontalTransverse_tangent,hi,Function.comp_def] using hd

theorem small_phase_derivative_cone {δ v : ℝ} (hδ : δ ≤ 1) (hv : |v| ≤ δ) (u : ℝ) :
    |Real.cosh u*Real.sin v| ≤ 2*δ*(Real.cosh u*Real.cos v) := by
  have hδ0 : 0 ≤ δ := (abs_nonneg v).trans hv
  have hv1 : v^2 ≤ 1 := (sq_le_one_iff_abs_le_one v).mpr (hv.trans hδ)
  have hc : (1 : ℝ)/2 ≤ Real.cos v := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]
  have hs : |Real.sin v| ≤ δ := Real.abs_sin_le_abs.trans hv
  rw [abs_mul,abs_of_pos (Real.cosh_pos u)]
  have hh : |Real.sin v| ≤ 2*δ*Real.cos v := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hh (Real.cosh_pos u).le]

theorem height_end_horizontal_secant_cone {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α x y₀ y₁ δ : ℝ) (hy : y₀ ≤ y₁) (hδ : δ ≤ 1)
    (hX : ∀ s ∈ Icc y₀ y₁, HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*((x : ℂ)+I*s)+F ((x : ℂ)+I*s))) 1))
        ((x : ℂ)+I*s))
    (hF : ∀ s ∈ Icc y₀ y₁, |(F ((x : ℂ)+I*s)).im| ≤ δ) :
    |endHorizontalTransverse (α*x) (X ((x : ℂ)+I*y₁))-
      endHorizontalTransverse (α*x) (X ((x : ℂ)+I*y₀))| ≤
      2*δ*(endHorizontalSupport (α*x) (X ((x : ℂ)+I*y₁))-
        endHorizontalSupport (α*x) (X ((x : ℂ)+I*y₀))) := by
  apply derivative_cone_secant_bound hy
    (fun s hs => height_end_support_hasDerivAt α x s (hX s hs))
    (fun s hs => height_end_transverse_hasDerivAt α x s (hX s hs))
  intro s hs
  exact small_phase_derivative_cone hδ (hF s hs) _

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_end_horizontal_secant_cone
