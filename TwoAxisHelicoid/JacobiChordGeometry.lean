import TwoAxisHelicoid.LeftComparisonPath

namespace TwoAxisHelicoid
open Complex Set Metric
set_option maxHeartbeats 800000

/-- A smaller disk containing the comparison arc and chord and staying away from
both singular values of the inverse Mobius map. -/
theorem jacobiChord_mem_ball {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {u : ℂ}
    (hre : h ≤ u.re) (hnorm : ‖u‖ ≤ 1) :
    u ∈ ball ((1/h : ℝ) : ℂ) (1/h-h/2) := by
  have hR : (0 : ℝ) < 1/h := one_div_pos.mpr hh
  have hmul : (1/h)*h = 1 := by field_simp
  have hRe : 1 ≤ (1/h)*u.re := by nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hre)]
  have hr : 0 < 1/h-h/2 := by nlinarith [sq_nonneg h]
  have hn := norm_nonneg u
  have hdist := norm_nonneg (u-((1/h : ℝ) : ℂ))
  have hs := Complex.sq_norm u
  have hd := Complex.sq_norm (u-((1/h : ℝ) : ℂ))
  simp only [normSq_apply] at hs
  simp only [normSq_apply, sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at hd
  apply mem_ball_iff_norm.mpr
  nlinarith [sq_nonneg (‖u-((1/h : ℝ) : ℂ)‖+(1/h-h/2))]

theorem jacobiChord_ball_re {h : ℝ} {u : ℂ}
    (hu : u ∈ ball ((1/h : ℝ) : ℂ) (1/h-h/2)) : h/2 < u.re := by
  have hd := mem_ball_iff_norm.mp hu
  have hb := (neg_le_abs (u-((1/h : ℝ) : ℂ)).re).trans (Complex.abs_re_le_norm _)
  simp only [sub_re, ofReal_re] at hb
  linarith

noncomputable def jacobiChordX (u : ℂ) : ℂ := (u+I)/(u-I)

theorem jacobiChord_den_ne_zero {u : ℂ} (hu : 0 < u.re) :
    u-I ≠ 0 ∧ u+I ≠ 0 := by
  constructor
  · intro he
    have h := congrArg Complex.re he
    simp only [sub_re, I_re, sub_zero, zero_re] at h
    linarith
  · intro he
    have h := congrArg Complex.re he
    simp only [add_re, I_re, add_zero, zero_re] at h
    linarith

theorem jacobiChordX_ne_zero {u : ℂ} (hu : 0 < u.re) : jacobiChordX u ≠ 0 :=
  div_ne_zero (jacobiChord_den_ne_zero hu).2 (jacobiChord_den_ne_zero hu).1

theorem jacobiChordX_norm_bounds {h : ℝ} (hh : 0 < h) {u : ℂ}
    (hu : h/2 < u.re) : ‖jacobiChordX u‖ ≤ 1+4/h ∧ ‖(jacobiChordX u)⁻¹‖ ≤ 1+4/h := by
  have hu0 : 0 < u.re := by linarith
  have hd := jacobiChord_den_ne_zero hu0
  have hdm : h/2 < ‖u-I‖ := by
    have hb := Complex.re_le_norm (u-I)
    simp only [sub_re, I_re, sub_zero] at hb
    linarith
  have hdp : h/2 < ‖u+I‖ := by
    have hb := Complex.re_le_norm (u+I)
    simp only [add_re, I_re, add_zero] at hb
    linarith
  have hb (d : ℝ) (hd : h/2 < d) : 2/d ≤ 4/h := by
    have hd0 : 0 < d := by linarith
    apply (div_le_div_iff₀ hd0 hh).mpr
    linarith
  have hx : jacobiChordX u = 1+2*I/(u-I) := by
    unfold jacobiChordX
    field_simp [hd.1]
    ring
  have hix : (jacobiChordX u)⁻¹ = 1-2*I/(u+I) := by
    unfold jacobiChordX
    rw [inv_div]
    field_simp [hd.2]
    ring
  constructor
  · rw [hx]
    calc
      _ ≤ ‖(1 : ℂ)‖+‖2*I/(u-I)‖ := norm_add_le _ _
      _ = 1+2/‖u-I‖ := by simp
      _ ≤ 1+4/h := by linarith [hb _ hdm]
  · rw [hix]
    calc
      _ ≤ ‖(1 : ℂ)‖+‖2*I/(u+I)‖ := norm_sub_le _ _
      _ = 1+2/‖u+I‖ := by simp
      _ ≤ 1+4/h := by linarith [hb _ hdp]

theorem jacobiChord_nome_bound {q : ℝ} (hq : 0 < q) (hqu : q ≤ 1/3) :
    q^2*(1+4/leftChordH q) < 1 := by
  have he : q^2*(1+4/leftChordH q) = q^2+2*q+2*q^3 := by
    unfold leftChordH
    field_simp [hq.ne', ne_of_gt (show (0 : ℝ) < 1+q^2 by positivity)]
    ring
  rw [he]
  have hq2 : q^2 ≤ (1/3 : ℝ)^2 := by nlinarith
  have hq3 : q^3 ≤ (1/3 : ℝ)^3 := by
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hq2)]
  nlinarith

theorem jacobiChord_ball_product_region {q : ℝ} (hq : 0 < q) (hqu : q ≤ 1/3) {u : ℂ}
    (hu : u ∈ ball ((1/leftChordH q : ℝ) : ℂ) (1/leftChordH q-leftChordH q/2)) :
    q^2*‖jacobiChordX u‖ < 1 ∧ q^2*‖(jacobiChordX u)⁻¹‖ < 1 := by
  have hb := jacobiChordX_norm_bounds (leftChordH_pos hq) (jacobiChord_ball_re hu)
  have hm := jacobiChord_nome_bound hq hqu
  constructor
  · exact (mul_le_mul_of_nonneg_left hb.1 (sq_nonneg q)).trans_lt hm
  · exact (mul_le_mul_of_nonneg_left hb.2 (sq_nonneg q)).trans_lt hm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiChord_ball_product_region
