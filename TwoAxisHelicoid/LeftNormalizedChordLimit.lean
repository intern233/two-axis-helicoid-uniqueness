import TwoAxisHelicoid.LeftChordAsymptoticIntegral
import TwoAxisHelicoid.LeftAsymptoticLimitTools

namespace TwoAxisHelicoid
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1000000
attribute [local irreducible] verticalA

theorem eighth_height_eventually_right :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t ∧ t ≤ 1/8 := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hu : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1/8 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/8)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hu] with t ht htu
  exact ⟨ht,htu.le⟩

noncomputable def leftNormalizedChordIntegral (t : ℝ) : ℝ :=
  (2*(leftKappa t)^2*Real.exp (-leftKappa t))*
    (∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
      leftChordRealKernel (leftKappa t) (leftChordH (leftNome t)) v)

theorem leftNormalizedChordIntegral_error_bound {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    |leftNormalizedChordIntegral t-1| ≤
      leftChordAsymptoticRemainder (leftKappa t) (leftChordH (leftNome t)) := by
  have hκ := leftKappa_gt ht htu
  have hκ0 : 0 < leftKappa t := by linarith
  rcases actual_left_chord_parameters ht htu with ⟨hh,hk,hsq,hκh⟩
  have hb := left_chord_parameter_estimates hκ hh hk hsq hκh
  have hkl : 1/2 ≤ leftChordK (leftNome t) := by
    have hh2 : (leftChordH (leftNome t))^2 ≤ 1/100 := by
      nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hb.1)]
    nlinarith
  have hJ := leftChordRealKernel_integral_asymptotic_bound (by linarith : 1 ≤ leftKappa t)
    hh (by linarith [hb.1] : leftChordH (leftNome t) ≤ 1) hkl hb.2.1 hsq
  have hscale : 0 < 2*(leftKappa t)^2*Real.exp (-leftKappa t) := by positivity
  have he : leftNormalizedChordIntegral t-1 =
      (2*(leftKappa t)^2*Real.exp (-leftKappa t))*
        ((∫ v : ℝ in (-leftChordK (leftNome t))..(leftChordK (leftNome t)),
          leftChordRealKernel (leftKappa t) (leftChordH (leftNome t)) v)-
          Real.exp (leftKappa t)/(2*(leftKappa t)^2)) := by
    unfold leftNormalizedChordIntegral
    rw [Real.exp_neg]
    field_simp [hκ0.ne',Real.exp_ne_zero (leftKappa t)]
  rw [he,abs_mul,abs_of_pos hscale,leftChordAsymptoticRemainder_eq_scaled hκ0.ne' hh.ne']
  exact mul_le_mul_of_nonneg_left hJ hscale.le

theorem leftNormalizedChordIntegral_tendsto_one :
    Tendsto leftNormalizedChordIntegral (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have ha : Tendsto (fun t : ℝ => |leftNormalizedChordIntegral t-1|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun _ => abs_nonneg _)
    · filter_upwards [eighth_height_eventually_right] with t ht
      exact leftNormalizedChordIntegral_error_bound ht.1 ht.2
    · exact leftChordAsymptoticRemainder_tendsto_zero
  have hd : Tendsto (fun t : ℝ => leftNormalizedChordIntegral t-1)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact ha
  simpa only [sub_add_cancel,zero_add] using hd.add_const 1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftNormalizedChordIntegral_tendsto_one
