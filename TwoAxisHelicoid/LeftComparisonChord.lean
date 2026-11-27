import TwoAxisHelicoid.LeftComparisonPath
import TwoAxisHelicoid.LeftChordKernel

namespace TwoAxisHelicoid
open Complex Set Metric MeasureTheory
set_option maxHeartbeats 800000
attribute [local irreducible] verticalA

theorem leftChord_point_mem_ball {h k v : ℝ} (hh : 0 < h)
    (hsq : h^2+k^2 = 1) (hv : v ∈ Icc (-k) k) :
    (h : ℂ)+I*(v : ℂ) ∈ ball ((1/h : ℝ) : ℂ) (1/h) := by
  apply leftComparison_mem_ball hh
  · simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, mul_zero, sub_self, add_zero, le_refl]
  · have hv2 : v^2 ≤ k^2 := by
      nlinarith [mul_nonneg (show 0 ≤ v+k by linarith [hv.1])
        (show 0 ≤ k-v by linarith [hv.2])]
    have hn := Complex.sq_norm ((h : ℂ)+I*(v : ℂ))
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
      I_re, I_im, zero_mul, mul_zero, one_mul, sub_self, add_zero, zero_add] at hn
    nlinarith [norm_nonneg ((h : ℂ)+I*(v : ℂ))]

theorem leftChord_primitive_difference {t κ h k : ℝ} (hh : 0 < h) (hk : 0 ≤ k)
    (hsq : h^2+k^2 = 1) {g : ℂ → ℂ}
    (hg : ∀ u ∈ ball ((1/h : ℝ) : ℂ) (1/h),
      HasDerivAt g (leftChordDifferential t κ u) u) :
    (∫ v : ℝ in (-k)..k, I*leftChordDifferential t κ ((h : ℂ)+I*(v : ℂ))) =
      g ((h : ℂ)+I*(k : ℂ))-g ((h : ℂ)-I*(k : ℂ)) := by
  have hab : -k ≤ k := by linarith
  have hd (v : ℝ) (hv : v ∈ Icc (-k) k) :
      HasDerivAt (fun x : ℝ => g ((h : ℂ)+I*(x : ℂ)))
        (I*leftChordDifferential t κ ((h : ℂ)+I*(v : ℂ))) v := by
    have harg := (((hasDerivAt_id v).ofReal_comp).const_mul I).const_add (h : ℂ)
    have hd := (hg _ (leftChord_point_mem_ball hh hsq hv)).comp v harg
    convert hd using 1
    · rfl
    · simp only [Complex.ofReal_one, mul_one]
      ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -k) (b := k)
    (fun v hv => hd v (by simpa only [uIcc_of_le hab] using hv))
    ((leftChordDifferential_line_continuous t κ hh.ne').intervalIntegrable _ _)
  simpa only [Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg] using hf

theorem leftComparisonPeriod_eq_chord {t : ℝ} (ht : 0 < t) :
    leftComparisonPeriod t = (Real.pi/(2*t))*
      ∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
        leftChordRealKernel (leftKappa t) (leftChordH (leftNome t)) v := by
  have hq0 := leftNome_pos t
  have hq1 : leftNome t < 1 := by
    unfold leftNome
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (by positivity)
  have hh := leftChordH_pos hq0
  have hk : 0 ≤ leftChordK (leftNome t) := by
    unfold leftChordK
    apply div_nonneg _ (by positivity)
    nlinarith
  obtain ⟨g,hg⟩ := leftChordDifferential_exact_ball t (dualProductKappa t (verticalA t))
    (one_div_pos.mpr hh)
  have hA := leftComparison_primitive_difference ht hg
  have hB := leftChord_primitive_difference hh hk (leftChordH_sq_add_K_sq (leftNome t)) hg
  have he : (∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)), I*leftComparisonFunction t (leftPathW y)) =
      -(∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
        I*leftChordDifferential t (dualProductKappa t (verticalA t))
          ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ))) := by
    rw [hA, hB]
    abel
  unfold leftComparisonPeriod
  rw [he, Complex.neg_re, neg_neg]
  have hre := intervalIntegral.intervalIntegral_re (μ := volume)
    (a := -leftChordK (leftNome t)) (b := leftChordK (leftNome t))
    ((leftChordDifferential_line_continuous t (dualProductKappa t (verticalA t)) hh.ne').intervalIntegrable _ _)
  change (∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
      (I*leftChordDifferential t (dualProductKappa t (verticalA t))
        ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ))).re) =
      (∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
        I*leftChordDifferential t (dualProductKappa t (verticalA t))
          ((leftChordH (leftNome t) : ℂ)+I*(v : ℂ))).re at hre
  rw [← hre]
  simp_rw [leftChordDifferential_re ht.ne' hh.ne']
  rw [intervalIntegral.integral_const_mul, ← leftKappa_eq_dualProductKappa ht]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftComparisonPeriod_eq_chord
