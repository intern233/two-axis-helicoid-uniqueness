import TwoAxisHelicoid.LeftArcGeometry

namespace TwoAxisHelicoid
open Complex Set Metric MeasureTheory
set_option maxHeartbeats 800000
attribute [local irreducible] verticalA

noncomputable def leftPathW (y : ℝ) : ℂ := (1/2 : ℂ)+I*(y : ℂ)
noncomputable def leftPathU (y : ℝ) : ℂ := leftMobius (jacobiExp (leftPathW y))
noncomputable def leftComparisonPeriod (t : ℝ) : ℝ :=
  -(∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)), I*leftComparisonFunction t (leftPathW y)).re

theorem leftPathW_hasDerivAt (y : ℝ) : HasDerivAt leftPathW I y := by
  convert (((hasDerivAt_id y).ofReal_comp).const_mul I).const_add (1/2 : ℂ) using 1
  · rfl
  · simp

theorem leftPathX_ne_one (y : ℝ) : jacobiExp (leftPathW y) ≠ 1 := by
  rw [leftPathW, jacobiExp_half_midline]
  intro h
  have hr := congrArg Complex.re h
  norm_num only [mul_re, I_re, I_im, ofReal_re, ofReal_im, zero_mul,
    mul_zero, sub_self, one_re] at hr

theorem leftPathU_eq_arc (y : ℝ) : leftPathU y = leftArcPoint (Real.exp (-Real.pi*y)) := by
  rw [leftPathU, leftPathW, jacobiExp_half_midline, leftMobius_I_mul_real]

theorem leftPathU_hasDerivAt (y : ℝ) :
    HasDerivAt leftPathU
      (((-2*I/(jacobiExp (leftPathW y)-1)^2)*
        (I*(Real.pi : ℂ)*jacobiExp (leftPathW y)))*I) y := by
  exact ((leftMobius_hasDerivAt (leftPathX_ne_one y)).comp (leftPathW y)
    (jacobiExp_hasDerivAt (leftPathW y))).comp y (leftPathW_hasDerivAt y)

theorem leftPathU_mem_ball {t y : ℝ} (_ht : 0 < t)
    (hy : y ∈ Icc (-(1/(2*t))) (1/(2*t))) :
    leftPathU y ∈ ball ((1/leftChordH (leftNome t) : ℝ) : ℂ) (1/leftChordH (leftNome t)) := by
  rw [leftPathU_eq_arc]
  apply leftComparison_mem_ball (leftChordH_pos (leftNome_pos t))
  · apply leftArcPoint_re_lower (leftNome_pos t)
    · unfold leftNome
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonpos_left hy.2 (neg_nonpos.mpr Real.pi_pos.le)
      convert h using 1
      ring
    · unfold leftNome
      rw [one_div, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonpos_left hy.1 (neg_nonpos.mpr Real.pi_pos.le)
      convert h using 1
      ring
  · exact (leftArcPoint_norm _).le

theorem leftPathU_endpoints (t : ℝ) :
    leftPathU (1/(2*t)) = (leftChordH (leftNome t) : ℂ)-I*(leftChordK (leftNome t) : ℂ) ∧
    leftPathU (-(1/(2*t))) = (leftChordH (leftNome t) : ℂ)+I*(leftChordK (leftNome t) : ℂ) := by
  have hpos : Real.exp (-Real.pi*(1/(2*t))) = leftNome t := by
    unfold leftNome
    congr 1
    ring
  have hneg : Real.exp (-Real.pi*(-(1/(2*t)))) = 1/leftNome t := by
    rw [← hpos]
    simp only [one_div]
    rw [← Real.exp_neg]
    congr 1
    ring
  constructor
  · rw [leftPathU_eq_arc, hpos, leftArcPoint_at_q]
  · rw [leftPathU_eq_arc, hneg, leftArcPoint_at_inv (leftNome_pos t).ne']

theorem leftComparison_path_continuous (t : ℝ) :
    Continuous (fun y : ℝ => I*leftComparisonFunction t (leftPathW y)) := by
  have hx : Continuous (fun y : ℝ => jacobiExp (leftPathW y)) := by
    rw [show (fun y => jacobiExp (leftPathW y)) =
        (fun y => I*(Real.exp (-Real.pi*y) : ℂ)) by
      funext y; exact jacobiExp_half_midline y]
    fun_prop
  unfold leftComparisonFunction dualProductMainTerm
  fun_prop (disch := intro y; exact sub_ne_zero.mpr (leftPathX_ne_one y).symm)

theorem leftComparison_primitive_difference {t : ℝ} (ht : 0 < t)
    {g : ℂ → ℂ}
    (hg : ∀ u ∈ ball ((1/leftChordH (leftNome t) : ℝ) : ℂ) (1/leftChordH (leftNome t)),
      HasDerivAt g (leftChordDifferential t (dualProductKappa t (verticalA t)) u) u) :
    (∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)), I*leftComparisonFunction t (leftPathW y)) =
      g ((leftChordH (leftNome t) : ℂ)-I*(leftChordK (leftNome t) : ℂ))-
      g ((leftChordH (leftNome t) : ℂ)+I*(leftChordK (leftNome t) : ℂ)) := by
  have hab : -(1/(2*t)) ≤ (1/(2*t)) := by
    have hp : 0 ≤ (1/(2*t)) := by positivity
    linarith
  have hd (y : ℝ) (hy : y ∈ Icc (-(1/(2*t))) (1/(2*t))) :
      HasDerivAt (fun s : ℝ => g (leftPathU s)) (I*leftComparisonFunction t (leftPathW y)) y := by
    have h := (hg _ (leftPathU_mem_ball ht hy)).comp y (leftPathU_hasDerivAt y)
    convert h using 1
    · rfl
    · rw [leftComparisonFunction_mobius ht (leftPathX_ne_one y)]
      unfold leftPathU
      ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -(1/(2*t))) (b := 1/(2*t))
    (fun y hy => hd y (by simpa only [uIcc_of_le hab] using hy))
    ((leftComparison_path_continuous t).intervalIntegrable _ _)
  rw [(leftPathU_endpoints t).1, (leftPathU_endpoints t).2] at hf
  exact hf

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftComparison_primitive_difference
