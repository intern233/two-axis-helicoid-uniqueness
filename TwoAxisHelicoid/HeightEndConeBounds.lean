import TwoAxisHelicoid.HeightEndCone

namespace TwoAxisHelicoid
open Complex Set

theorem endHorizontalTransverse_bound (θ : ℝ) {v : Fin 3 → ℝ} {B : ℝ}
    (h0 : |v 0| ≤ B) (h1 : |v 1| ≤ B) :
    |endHorizontalTransverse θ v| ≤ 2*B := by
  rw [endHorizontalTransverse_apply]
  calc |Real.cos θ*v 0+Real.sin θ*v 1| ≤ |Real.cos θ*v 0|+|Real.sin θ*v 1| := abs_add_le _ _
       _ ≤ 1*B+1*B := by
         rw [abs_mul,abs_mul]
         exact add_le_add
           (mul_le_mul (Real.abs_cos_le_one θ) h0 (abs_nonneg _) (by norm_num))
           (mul_le_mul (Real.abs_sin_le_one θ) h1 (abs_nonneg _) (by norm_num))
       _ = 2*B := by ring

theorem cone_from_bounded_vertex {r t r₀ t₀ δ C : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hC : 0 ≤ C)
    (hr₀ : |r₀| ≤ C) (ht₀ : |t₀| ≤ C)
    (hsec : |t-t₀| ≤ 2*δ*|r-r₀|) (hfar : 3*C ≤ δ*|r|) :
    |t| ≤ 3*δ*|r| := by
  have ht := abs_add_le (t-t₀) t₀
  rw [sub_add_cancel] at ht
  have hr : |r-r₀| ≤ |r|+C := (abs_sub r r₀).trans (by linarith)
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*δ by positivity)
  have hδC : δ*C ≤ C := by nlinarith
  nlinarith

/-- If a horizontal level passes through the vertical axis and its
tangent phases are small, its entire image stays in a narrow double cone. -/
theorem height_end_axis_level_cone {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α x y δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hX : ∀ s : ℝ, HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*((x : ℂ)+I*s)+F ((x : ℂ)+I*s))) 1))
        ((x : ℂ)+I*s))
    (hF : ∀ s : ℝ, |(F ((x : ℂ)+I*s)).im| ≤ δ)
    (haxis : X (x : ℂ) 0 = 0 ∧ X (x : ℂ) 1 = 0) :
    |endHorizontalTransverse (α*x) (X ((x : ℂ)+I*y))| ≤
      2*δ*|endHorizontalSupport (α*x) (X ((x : ℂ)+I*y))| := by
  have hr₀ : endHorizontalSupport (α*x) (X ((x : ℂ)+I*(0 : ℝ))) = 0 := by
    simp [endHorizontalSupport_apply,haxis.1,haxis.2]
  have ht₀ : endHorizontalTransverse (α*x) (X ((x : ℂ)+I*(0 : ℝ))) = 0 := by
    simp [endHorizontalTransverse_apply,haxis.1,haxis.2]
  rcases le_total 0 y with hy | hy
  · have hh := height_end_horizontal_secant_cone α x 0 y δ hy hδ
      (fun s _ => hX s) (fun s _ => hF s)
    rw [hr₀,ht₀,sub_zero,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  · have hh := height_end_horizontal_secant_cone α x y 0 δ hy hδ
      (fun s _ => hX s) (fun s _ => hF s)
    rw [hr₀,ht₀,zero_sub,zero_sub,abs_neg] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_end_axis_level_cone
