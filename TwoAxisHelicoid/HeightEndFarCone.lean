import TwoAxisHelicoid.HeightEndConeBounds

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 1000000

/-- Uniform cone control on the high positive and negative imaginary
tails, allowing a bounded starting point at each height. -/
theorem height_end_far_vertical_cone {X : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ}
    (α x Y C δ y : ℝ) (hC : 0 ≤ C) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hX : ∀ z : ℂ, Y ≤ ‖z‖ → HasFDerivAt X
      (nullRealDerivative (weierstrassTriple (exp (I*α*z+F z)) 1)) z)
    (hF : ∀ z : ℂ, Y ≤ ‖z‖ → |(F z).im| ≤ δ)
    (hbase : ∀ s ∈ ({-Y,Y} : Set ℝ),
      |endHorizontalSupport (α*x) (X ((x : ℂ)+I*s))| ≤ C ∧
      |endHorizontalTransverse (α*x) (X ((x : ℂ)+I*s))| ≤ C)
    (hy : Y ≤ |y|) (hfar : 3*C ≤ δ*((|y|-Y)/2-C)) :
    |endHorizontalTransverse (α*x) (X ((x : ℂ)+I*y))| ≤
      3*δ*|endHorizontalSupport (α*x) (X ((x : ℂ)+I*y))| := by
  let r : ℝ → ℝ := fun s => endHorizontalSupport (α*x) (X ((x : ℂ)+I*s))
  let t : ℝ → ℝ := fun s => endHorizontalTransverse (α*x) (X ((x : ℂ)+I*s))
  have hmul : 0 ≤ 2*δ := by positivity
  rcases le_total 0 y with hy0 | hy0
  · have hYy : Y ≤ y := by simpa only [abs_of_nonneg hy0] using hy
    have hn s (hs : s ∈ Icc Y y) : Y ≤ ‖(x : ℂ)+I*s‖ :=
      hs.1.trans ((le_abs_self s).trans (vertical_line_norm_ge_abs x s))
    have hg := height_end_support_interval_growth α x Y y hYy
      (fun s hs => hX _ (hn s hs)) (fun s hs => (hF _ (hn s hs)).trans hδ)
    change (y-Y)/2 ≤ r y-r Y at hg
    have hc := height_end_horizontal_secant_cone α x Y y δ hYy hδ
      (fun s hs => hX _ (hn s hs)) (fun s hs => hF _ (hn s hs))
    change |t y-t Y| ≤ 2*δ*(r y-r Y) at hc
    have hb := hbase Y (by simp)
    have hl : (|y|-Y)/2-C ≤ |r y| := by
      have hrbase := (abs_le.mp hb.1).1
      change -C ≤ r Y at hrbase
      rw [abs_of_nonneg hy0]
      linarith [le_abs_self (r y)]
    exact cone_from_bounded_vertex hδ0 hδ hC hb.1 hb.2
      (hc.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hmul))
      (hfar.trans (mul_le_mul_of_nonneg_left hl hδ0))
  · have hyY : y ≤ -Y := by
      rw [abs_of_nonpos hy0] at hy
      linarith
    have hn s (hs : s ∈ Icc y (-Y)) : Y ≤ ‖(x : ℂ)+I*s‖ := by
      have hh : Y ≤ -s := by linarith [hs.2]
      exact hh.trans ((neg_le_abs s).trans (vertical_line_norm_ge_abs x s))
    have hg := height_end_support_interval_growth α x y (-Y) hyY
      (fun s hs => hX _ (hn s hs)) (fun s hs => (hF _ (hn s hs)).trans hδ)
    change (-Y-y)/2 ≤ r (-Y)-r y at hg
    have hc := height_end_horizontal_secant_cone α x y (-Y) δ hyY hδ
      (fun s hs => hX _ (hn s hs)) (fun s hs => hF _ (hn s hs))
    change |t (-Y)-t y| ≤ 2*δ*(r (-Y)-r y) at hc
    have hc' : |t y-t (-Y)| ≤ 2*δ*|r y-r (-Y)| := by
      rw [abs_sub_comm (t y),abs_sub_comm (r y)]
      exact hc.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hmul)
    have hb := hbase (-Y) (by simp)
    have hl : (|y|-Y)/2-C ≤ |r y| := by
      have hrbase := (abs_le.mp hb.1).2
      change r (-Y) ≤ C at hrbase
      rw [abs_of_nonpos hy0]
      linarith [neg_le_abs (r y)]
    exact cone_from_bounded_vertex hδ0 hδ hC hb.1 hb.2 hc'
      (hfar.trans (mul_le_mul_of_nonneg_left hl hδ0))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.height_end_far_vertical_cone
