import TwoAxisHelicoid.HeightEndProper

namespace TwoAxisHelicoid
open Complex Set

/-- A level curve cannot intersect itself on a sufficiently far subend.
The two components separated by the inner disk are distinguished by the
same horizontal support which is monotone on each component. -/
theorem height_end_level_injective {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α x R₀ Y C : ℝ) (hRY : R₀ < Y) (hC : 0 ≤ C)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+F z)) 1)) z)
    (hF : ∀ z : ℂ, Y ≤ ‖z‖ → |(F z).im| ≤ 1)
    (hbase : |x| ≤ Y →
      |endHorizontalSupport (α*x) (X ((x : ℂ)+I*Y))| ≤ C ∧
      |endHorizontalSupport (α*x) (X ((x : ℂ)+I*(-Y)))| ≤ C)
    {y₀ y₁ : ℝ} (h₀ : 2*Y+2*C+1 ≤ ‖(x : ℂ)+I*y₀‖)
    (h₁ : 2*Y+2*C+1 ≤ ‖(x : ℂ)+I*y₁‖)
    (he : X ((x : ℂ)+I*y₀) = X ((x : ℂ)+I*y₁)) : y₀ = y₁ := by
  wlog hy : y₀ ≤ y₁ generalizing y₀ y₁
  · exact (this h₁ h₀ he.symm (le_of_not_ge hy)).symm
  have hs := congrArg (endHorizontalSupport (α*x)) he
  have hgrowth (u v : ℝ) (huv : u ≤ v)
      (hn : ∀ s ∈ Icc u v, Y ≤ ‖(x : ℂ)+I*s‖) :
      (v-u)/2 ≤ endHorizontalSupport (α*x) (X ((x : ℂ)+I*v))-
        endHorizontalSupport (α*x) (X ((x : ℂ)+I*u)) :=
    height_end_support_interval_growth α x u v huv
      (fun s hs => hX _ (hRY.trans_le (hn s hs))) (fun s hs => hF _ (hn s hs))
  have finish (hn : ∀ s ∈ Icc y₀ y₁, Y ≤ ‖(x : ℂ)+I*s‖) : y₀ = y₁ := by
    have hg := hgrowth y₀ y₁ hy hn
    rw [hs,sub_self] at hg
    linarith
  by_cases hx : Y ≤ |x|
  · apply finish
    intro s _
    exact hx.trans (by simpa using Complex.abs_re_le_norm ((x : ℂ)+I*s))
  have hxY : |x| ≤ Y := (not_le.mp hx).le
  have hab₀ : Y+2*C+1 ≤ |y₀| := by
    have hn : ‖(x : ℂ)+I*y₀‖ ≤ |x|+|y₀| := by
      simpa using Complex.norm_le_abs_re_add_abs_im ((x : ℂ)+I*y₀)
    linarith
  have hab₁ : Y+2*C+1 ≤ |y₁| := by
    have hn : ‖(x : ℂ)+I*y₁‖ ≤ |x|+|y₁| := by
      simpa using Complex.norm_le_abs_re_add_abs_im ((x : ℂ)+I*y₁)
    linarith
  by_cases hpos : Y ≤ y₀
  · apply finish
    intro s hs
    exact (hpos.trans hs.1).trans ((le_abs_self s).trans (vertical_line_norm_ge_abs x s))
  by_cases hneg : y₁ ≤ -Y
  · apply finish
    intro s hs
    have hn : Y ≤ -s := by linarith [hs.2]
    exact hn.trans ((neg_le_abs s).trans (vertical_line_norm_ge_abs x s))
  have hy₀ : y₀ < 0 := by
    by_contra hn
    rw [abs_of_nonneg (le_of_not_gt hn)] at hab₀
    linarith [not_le.mp hpos]
  have hy₁ : 0 < y₁ := by
    by_contra hn
    rw [abs_of_nonpos (le_of_not_gt hn)] at hab₁
    linarith [not_le.mp hneg]
  rw [abs_of_neg hy₀] at hab₀
  rw [abs_of_pos hy₁] at hab₁
  have hn := hgrowth y₀ (-Y) (by linarith) (by
    intro s hs
    have hh : Y ≤ -s := by linarith [hs.2]
    exact hh.trans ((neg_le_abs s).trans (vertical_line_norm_ge_abs x s)))
  have hp := hgrowth Y y₁ (by linarith) (by
    intro s hs
    exact hs.1.trans ((le_abs_self s).trans (vertical_line_norm_ge_abs x s)))
  simp only [Complex.ofReal_neg] at hn
  have hbp := (abs_le.mp (hbase hxY).1).1
  have hbn := (abs_le.mp (hbase hxY).2).2
  rw [hs] at hn
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_end_level_injective
