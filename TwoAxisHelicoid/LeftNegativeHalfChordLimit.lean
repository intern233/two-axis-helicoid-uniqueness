import TwoAxisHelicoid.LeftNormalizedChordLimit
import TwoAxisHelicoid.LeftVerticalAsymptotic

namespace TwoAxisHelicoid
open Set Filter MeasureTheory Asymptotics
open scoped Topology
attribute [local irreducible] verticalA jacobiRealE

private theorem half_chord_ratio_error {κ h k : ℝ}
    (hκ : 1 ≤ κ) (hh : 0 < h) (hu : h ≤ 1) (hk : 0 ≤ k) (ku : k ≤ 1)
    (circle : h^2+k^2 = 1) :
    |(∫ v : ℝ in (-k)..0, leftChordRealKernel κ h v)/(Real.exp κ/(2*κ^2))-1| ≤
      leftChordAsymptoticRemainder κ h := by
  have kp : 0 < κ := by linarith
  have cont := leftChordRealKernel_continuous hh.ne' κ
  have split := intervalIntegral.integral_add_adjacent_intervals
    (cont.intervalIntegrable (μ := volume) (-1) (-k)) (cont.intervalIntegrable (-k) 0)
  have strip := leftChordRealKernel_end_strip_integral_bound kp.le hh hk ku circle
  have neg := leftChordRealKernel_negative_integral_remainder hκ hh hu
  have scale : 0 ≤ 2*κ^2*Real.exp (-κ) := by positivity
  have normalize (x : ℝ) : x/(Real.exp κ/(2*κ^2))-1 =
      (2*κ^2*Real.exp (-κ))*(x-Real.exp κ/(2*κ^2)) := by
    rw [Real.exp_neg]
    field_simp [kp.ne', Real.exp_ne_zero κ]
  rw [normalize,abs_mul,abs_of_nonneg scale,leftChordAsymptoticRemainder_eq_scaled kp.ne' hh.ne']
  apply mul_le_mul_of_nonneg_left _ scale
  have diff : (∫ v : ℝ in (-k)..0, leftChordRealKernel κ h v)-Real.exp κ/(2*κ^2) =
      ((∫ v : ℝ in (-1)..0, leftChordRealKernel κ h v)-Real.exp κ/(2*κ^2))-
        (∫ v : ℝ in (-1)..(-k), leftChordRealKernel κ h v) := by linarith only [split]
  rw [diff]
  refine ((abs_sub _ _).trans (add_le_add neg strip)).trans ?_
  have extra : 0 ≤ 2+κ+Real.exp (-κ/2)*(1/h+2*κ) := by positivity
  linarith only [extra]

/-- Appendix B.1, line 2199, for the literal negative half of the chord.
The height, chord and nome parameters all belong to the actual vertical branch. -/
theorem left_negative_half_chord_ratio_tendsto_one :
    Tendsto (fun t : ℝ =>
      let κ := leftKappa t
      let h := leftChordH (leftNome t)
      let k := leftChordK (leftNome t)
      (∫ v : ℝ in (-k)..0, Real.exp (-κ*v)*
        (((k^2-v^2)*Real.cos (κ*h)+2*h*Real.sin (κ*h))/(h^2+(v-1)^2))) /
        (Real.exp κ/(2*κ^2))) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  let J := fun t : ℝ => (∫ v : ℝ in (-leftChordK (leftNome t))..0,
    leftChordRealKernel (leftKappa t) (leftChordH (leftNome t)) v) /
      (Real.exp (leftKappa t)/(2*(leftKappa t)^2))
  have herr : Tendsto (fun t : ℝ => |J t-1|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ leftChordAsymptoticRemainder_tendsto_zero
    filter_upwards [eighth_height_eventually_right] with t ht
    have hκ := leftKappa_gt ht.1 ht.2
    obtain ⟨hh,hk,circle,small⟩ := actual_left_chord_parameters ht.1 ht.2
    have limits := left_chord_parameter_estimates hκ hh hk circle small
    exact half_chord_ratio_error (by linarith) hh (by linarith [limits.1]) hk limits.2.1 circle
  have hd : Tendsto (fun t : ℝ => J t-1) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr herr
  have hj : Tendsto J (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa only [sub_add_cancel,zero_add] using hd.add_const 1
  apply hj.congr'
  filter_upwards [eighth_height_eventually_right] with t ht
  have circle := (actual_left_chord_parameters ht.1 ht.2).2.2.1
  have ksq : 1-(leftChordH (leftNome t))^2 = (leftChordK (leftNome t))^2 := by linarith
  simp only [J,leftChordRealKernel,ksq]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_negative_half_chord_ratio_tendsto_one
