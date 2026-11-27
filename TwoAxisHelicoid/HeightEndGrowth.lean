import TwoAxisHelicoid.HeightEndSupport
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TwoAxisHelicoid
open Complex Set

theorem height_end_support_interval_growth {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α x y₀ y₁ : ℝ) (hy : y₀ ≤ y₁)
    (hX : ∀ s ∈ Icc y₀ y₁, HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*((x : ℂ)+I*s)+F ((x : ℂ)+I*s))) 1))
        ((x : ℂ)+I*s))
    (hF : ∀ s ∈ Icc y₀ y₁, |(F ((x : ℂ)+I*s)).im| ≤ 1) :
    (y₁-y₀)/2 ≤ endHorizontalSupport (α*x) (X ((x : ℂ)+I*y₁))-
      endHorizontalSupport (α*x) (X ((x : ℂ)+I*y₀)) := by
  have hd s hs := height_end_support_hasDerivAt α x s (hX s hs)
  have h := (convex_Icc y₀ y₁).mul_sub_le_image_sub_of_le_deriv
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => height_end_support_deriv_lower α x s (hX s (interior_subset hs))
      (hF s (interior_subset hs)))
    y₀ (left_mem_Icc.mpr hy) y₁ (right_mem_Icc.mpr hy) hy
  linarith

theorem vertical_line_norm_ge_abs (x y : ℝ) : |y| ≤ ‖(x : ℂ)+I*y‖ := by
  simpa using Complex.abs_im_le_norm ((x : ℂ)+I*y)

theorem height_end_vertical_escape_bound {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α x R₀ Y B C : ℝ) (hY : 0 ≤ Y) (hRY : R₀ < Y) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+F z)) 1)) z)
    (hF : ∀ z : ℂ, Y ≤ ‖z‖ → |(F z).im| ≤ 1)
    (hbase : ∀ ε ∈ ({-1,1} : Set ℝ),
      |X ((x : ℂ)+I*(ε*Y)) 0| ≤ C ∧ |X ((x : ℂ)+I*(ε*Y)) 1| ≤ C)
    {y : ℝ} (hy0 : |X ((x : ℂ)+I*y) 0| ≤ B) (hy1 : |X ((x : ℂ)+I*y) 1| ≤ B) :
    |y| ≤ Y+4*(B+C) := by
  have hsupport := endHorizontalSupport_bound (α*x) hy0 hy1
  have hbplus : |X ((x : ℂ)+I*Y) 0| ≤ C ∧ |X ((x : ℂ)+I*Y) 1| ≤ C := by
    simpa only [Complex.ofReal_one,one_mul] using hbase 1 (by simp)
  have hbminus : |X ((x : ℂ)+I*(-Y)) 0| ≤ C ∧ |X ((x : ℂ)+I*(-Y)) 1| ≤ C := by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_mul,one_mul] using hbase (-1) (by simp)
  have hsplus := endHorizontalSupport_bound (α*x) hbplus.1 hbplus.2
  have hsminus := endHorizontalSupport_bound (α*x) hbminus.1 hbminus.2
  rcases le_total Y y with hy | hy
  · have hn (s : ℝ) (hs : s ∈ Icc Y y) : Y ≤ ‖(x : ℂ)+I*s‖ :=
      hs.1.trans ((le_abs_self s).trans (vertical_line_norm_ge_abs x s))
    have hg := height_end_support_interval_growth α x Y y hy
      (fun s hs => hX _ (hRY.trans_le (hn s hs))) (fun s hs => hF _ (hn s hs))
    rw [abs_of_nonneg (hY.trans hy)]
    have h1 := (abs_le.mp hsupport).2
    have h2 := (abs_le.mp hsplus).1
    linarith
  · rcases le_total y (-Y) with hyn | hyn
    · have hn (s : ℝ) (hs : s ∈ Icc y (-Y)) : Y ≤ ‖(x : ℂ)+I*s‖ := by
        have hneg : Y ≤ -s := by linarith [hs.2]
        exact hneg.trans ((neg_le_abs s).trans (vertical_line_norm_ge_abs x s))
      have hg := height_end_support_interval_growth α x y (-Y) hyn
        (fun s hs => hX _ (hRY.trans_le (hn s hs))) (fun s hs => hF _ (hn s hs))
      simp only [Complex.ofReal_neg] at hg
      rw [abs_of_nonpos (by linarith)]
      have h1 := (abs_le.mp hsupport).1
      have h2 := (abs_le.mp hsminus).2
      linarith
    · have hab : |y| ≤ Y := abs_le.mpr ⟨hyn,hy⟩
      linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_end_vertical_escape_bound
