import TwoAxisHelicoid.SlopingFluxBounds

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaA

/-- Reflection over the midpoint of the original parameter interval
expresses the imaginary handle period by the checked paired integrand. -/
theorem original_sloping_imaginary_eq_reflected_integral {t : ℝ} (ht : 0 < t) (a : ℝ) :
    (originalSlopingPeriod t a).im = ∫ s : ℝ in 0..1, reflectedSlopingFlux t a s := by
  let f (s : ℝ) := thetaA t a (originalPeriodPath t s)
  let V : ℂ := (1-I*t)/2
  have hcont : ContinuousOn f (Icc (-1:ℝ) 1) := (thetaA_holomorphic_original_rectangle ht a).continuousOn.comp
    (by unfold originalPeriodPath; fun_prop) (fun s hs => originalPeriodPath_mem_rectangle ht hs)
  have hplus : IntervalIntegrable f volume 0 1 := (hcont.mono (show Icc (0:ℝ) 1 ⊆ Icc (-1:ℝ) 1 from Icc_subset_Icc_left (by norm_num))).intervalIntegrable_of_Icc zero_le_one
  have hleft : IntervalIntegrable f volume (-1) 0 := (hcont.mono (show Icc (-1:ℝ) 0 ⊆ Icc (-1:ℝ) 1 from Icc_subset_Icc_right (by norm_num))).intervalIntegrable_of_Icc (by norm_num : (-1:ℝ) ≤ 0)
  have hminus : IntervalIntegrable (fun s => f (-s)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply hcont.comp continuous_neg.continuousOn
    intro s hs
    exact ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hpair : (∫ s : ℝ in 0..1, f s+f (-s)) = ∫ s : ℝ in (-1)..1, f s := by
    rw [intervalIntegral.integral_add hplus hminus,intervalIntegral.integral_comp_neg,neg_zero,add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals hleft hplus
  have h := Complex.imCLM.intervalIntegral_comp_comm ((hplus.add hminus).const_mul V)
  change (V*(∫ s : ℝ in (-1)..1, f s)).im = ∫ s : ℝ in 0..1, (V*(f s+f (-s))).im
  rw [← hpair,← intervalIntegral.integral_const_mul]
  exact h.symm

theorem original_sloping_imaginary_negative_of_reflected {t a : ℝ} (ht : 0 < t)
    (h : ∀ s ∈ Icc (0:ℝ) 1, reflectedSlopingFlux t a s ≤ -(1/32:ℝ)) :
    (originalSlopingPeriod t a).im ≤ -(1/32:ℝ) := by
  rw [original_sloping_imaginary_eq_reflected_integral ht a]
  have hp : ContinuousOn (fun s => thetaA t a (originalPeriodPath t s)) (Icc (0:ℝ) 1) :=
    (thetaA_holomorphic_original_rectangle ht a).continuousOn.comp (by unfold originalPeriodPath; fun_prop)
      (fun s hs => originalPeriodPath_mem_rectangle ht ⟨by linarith [hs.1],hs.2⟩)
  have hm : ContinuousOn (fun s => thetaA t a (originalPeriodPath t (-s))) (Icc (0:ℝ) 1) :=
    (thetaA_holomorphic_original_rectangle ht a).continuousOn.comp (by unfold originalPeriodPath; fun_prop)
      (fun s hs => originalPeriodPath_mem_rectangle ht ⟨by linarith [hs.2],by linarith [hs.1]⟩)
  have hf : IntervalIntegrable (reflectedSlopingFlux t a) volume 0 1 :=
    (Complex.continuous_im.comp_continuousOn (continuousOn_const.mul (hp.add hm))).intervalIntegrable_of_Icc zero_le_one
  simpa using intervalIntegral.integral_mono_on zero_le_one hf (intervalIntegrable_const (b := 1)) h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_sloping_imaginary_negative_of_reflected
