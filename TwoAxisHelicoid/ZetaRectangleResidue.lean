import TwoAxisHelicoid.ZetaPoleRegular
import TwoAxisHelicoid.RectanglePoleIntegral

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaSigma thetaZeta zetaPoleRegular

def RectangleIntegrable (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ)-(b : ℂ)*I)) volume (-a) a ∧
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(b : ℂ)*I)) volume (-a) a ∧
  IntervalIntegrable (fun y : ℝ => f ((a : ℂ)+(y : ℂ)*I)) volume (-b) b ∧
  IntervalIntegrable (fun y : ℝ => f (-(a : ℂ)+(y : ℂ)*I)) volume (-b) b

theorem rectangleBoundary_add {f g : ℂ → ℂ} {a b : ℝ}
    (hf : RectangleIntegrable f a b) (hg : RectangleIntegrable g a b) :
    rectangleBoundary (fun z => f z+g z) a b = rectangleBoundary f a b+rectangleBoundary g a b := by
  simp only [rectangleBoundary,intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem rectangleBoundary_congr {f g : ℂ → ℂ} {a b : ℝ}
    (hb : ∀ x ∈ uIcc (-a) a, f ((x : ℂ)-(b : ℂ)*I) = g ((x : ℂ)-(b : ℂ)*I))
    (ht : ∀ x ∈ uIcc (-a) a, f ((x : ℂ)+(b : ℂ)*I) = g ((x : ℂ)+(b : ℂ)*I))
    (hr : ∀ y ∈ uIcc (-b) b, f ((a : ℂ)+(y : ℂ)*I) = g ((a : ℂ)+(y : ℂ)*I))
    (hl : ∀ y ∈ uIcc (-b) b, f (-(a : ℂ)+(y : ℂ)*I) = g (-(a : ℂ)+(y : ℂ)*I)) :
    rectangleBoundary f a b = rectangleBoundary g a b := by
  unfold rectangleBoundary
  rw [intervalIntegral.integral_congr hb,intervalIntegral.integral_congr ht,
    intervalIntegral.integral_congr hr,intervalIntegral.integral_congr hl]

theorem central_rectangle_horizontal_mem {t a x : ℝ} (ht : 0 < t) (ha : a < 1)
    (hx : x ∈ Icc (-a) a) (s : ℝ) (hs : |s| ≤ t) :
    (x : ℂ)+(s : ℂ)*I ∈ complexOpenRect (-1) 1 (-2*t) (2*t) := by
  have hb := abs_le.mp hs
  constructor <;> constructor <;> dsimp <;> simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,sub_zero,zero_add,add_zero] <;> linarith [hx.1,hx.2]

theorem central_rectangle_vertical_mem {t a y : ℝ} (ht : 0 < t) (ha : |a| < 1)
    (hy : y ∈ Icc (-t) t) :
    (a : ℂ)+(y : ℂ)*I ∈ complexOpenRect (-1) 1 (-2*t) (2*t) := by
  have ha' := abs_lt.mp ha
  constructor <;> constructor <;> dsimp <;> simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,sub_zero,zero_add,add_zero] <;> linarith [hy.1,hy.2]

theorem zetaPoleRegular_rectangle_integrable {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) :
    RectangleIntegrable (zetaPoleRegular t) a t := by
  have hc := (zetaPoleRegular_differentiableOn_central_rectangle ht).continuousOn
  have hh (s : ℝ) (hs : |s| ≤ t) :
      IntervalIntegrable (fun x : ℝ => zetaPoleRegular t ((x : ℂ)+(s : ℂ)*I)) volume (-a) a := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [ha.1] : -a ≤ a)
    exact hc.comp (by fun_prop) (fun x hx => central_rectangle_horizontal_mem ht ha.2 hx s hs)
  have hv (s : ℝ) (hs : |s| < 1) :
      IntervalIntegrable (fun y : ℝ => zetaPoleRegular t ((s : ℂ)+(y : ℂ)*I)) volume (-t) t := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith : -t ≤ t)
    exact hc.comp (by fun_prop) (fun y hy => central_rectangle_vertical_mem ht hs hy)
  refine ⟨?_,hh t (by simp [abs_of_pos ht]),hv a (by simpa [abs_of_pos ha.1] using ha.2),?_⟩
  · simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using hh (-t) (by simp [abs_of_pos ht])
  · simpa only [Complex.ofReal_neg] using hv (-a) (by simpa [abs_of_pos ha.1] using ha.2)

theorem rectangle_inv_integrable {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    RectangleIntegrable (fun z : ℂ => z⁻¹) a b := by
  refine ⟨?_,(inverse_horizontal_continuous b hb).intervalIntegrable _ _,
    (inverse_vertical_continuous a ha).intervalIntegrable _ _,?_⟩
  · simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
      (inverse_horizontal_continuous (-b) (neg_ne_zero.mpr hb)).intervalIntegrable (μ := volume) (-a) a
  · simpa only [Complex.ofReal_neg] using
      (inverse_vertical_continuous (-a) (neg_ne_zero.mpr ha)).intervalIntegrable (μ := volume) (-b) b

/-- The central rhombic rectangle encloses exactly the residue-one pole at zero. -/
theorem thetaZeta_rectangle_residue {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) :
    rectangleBoundary (thetaZeta t) a t = 2*Real.pi*I := by
  have heq {z : ℂ} (hz : z ∈ complexOpenRect (-1) 1 (-2*t) (2*t)) (hn : z ≠ 0) :
      thetaZeta t z = z⁻¹+zetaPoleRegular t z := by
    apply thetaZeta_eq_inv_add_regular ht
    intro hL
    exact hn (rhombic_central_rectangle_lattice ht hz hL)
  have hc : rectangleBoundary (thetaZeta t) a t =
      rectangleBoundary (fun z : ℂ => z⁻¹+zetaPoleRegular t z) a t := by
    apply rectangleBoundary_congr
    · intro x hx
      rw [uIcc_of_le (by linarith [ha.1] : -a ≤ a)] at hx
      apply heq
      · simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
          central_rectangle_horizontal_mem ht ha.2 hx (-t) (by simp [abs_of_pos ht])
      · intro hz
        have hi := congrArg Complex.im hz
        norm_num at hi
        linarith
    · intro x hx
      rw [uIcc_of_le (by linarith [ha.1] : -a ≤ a)] at hx
      apply heq (central_rectangle_horizontal_mem ht ha.2 hx t (by simp [abs_of_pos ht]))
      intro hz
      have hi := congrArg Complex.im hz
      norm_num at hi
      linarith
    · intro y hy
      rw [uIcc_of_le (by linarith : -t ≤ t)] at hy
      apply heq (central_rectangle_vertical_mem ht (by simpa [abs_of_pos ha.1] using ha.2) hy)
      intro hz
      have hr := congrArg Complex.re hz
      norm_num at hr
      linarith [ha.1]
    · intro y hy
      rw [uIcc_of_le (by linarith : -t ≤ t)] at hy
      apply heq
      · simpa only [Complex.ofReal_neg] using
          central_rectangle_vertical_mem ht (a := -a) (by simpa [abs_of_pos ha.1] using ha.2) hy
      · intro hz
        have hr := congrArg Complex.re hz
        norm_num at hr
        linarith [ha.1]
  rw [hc,rectangleBoundary_add (rectangle_inv_integrable ha.1.ne' ht.ne')
    (zetaPoleRegular_rectangle_integrable ht ha),rectangleBoundary_inv ha.1 ht]
  have hzero : rectangleBoundary (zetaPoleRegular t) a t = 0 := by
    apply rectangleBoundary_holomorphic_zero (zetaPoleRegular_differentiableOn_central_rectangle ht)
    · simpa only [Complex.ofReal_neg,neg_mul,sub_eq_add_neg] using
        central_rectangle_horizontal_mem ht ha.2
          (show -a ∈ Icc (-a) a from ⟨le_rfl,by linarith [ha.1]⟩) (-t) (by simp [abs_of_pos ht])
    · exact central_rectangle_horizontal_mem ht ha.2
        ⟨by linarith [ha.1],le_rfl⟩ t (by simp [abs_of_pos ht])
  rw [hzero,add_zero]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_rectangle_residue
