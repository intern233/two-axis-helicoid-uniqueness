import TwoAxisHelicoid.JacobiRootAsymptotic
import Mathlib.Analysis.Asymptotics.Lemmas

namespace TwoAxisHelicoid
open Set Filter Asymptotics
open scoped Topology
set_option maxHeartbeats 800000
attribute [local irreducible] verticalA

theorem leftEpsilon_eq_vertical_displacement (t : ℝ) :
    leftEpsilon t = Real.pi*(verticalA t-1/2)/t := by
  unfold leftEpsilon leftNome leftRootR
  rw [Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp,Real.log_exp]
  ring

theorem leftEpsilon_second_remainder {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    |leftEpsilon t-2*leftNome t| ≤ 64*(leftNome t)^2 := by
  have hr := leftRootR_bounds ht htu
  exact jacobi_root_log_second_remainder (leftNome_pos t)
    (leftNome_lt_one_hundredth ht htu).le hr.1 hr.2
    (jacobiRealE_at_verticalA_zero (small_height_mem_vertical_domain ht htu))

/-- The first left-end asymptotic formula in Appendix B.1, with an explicit
remainder constant on a whole interval of positive parameters. -/
theorem verticalA_left_asymptotic_error_bound {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    |verticalA t-1/2-(2*t/Real.pi)*Real.exp (-Real.pi/(2*t))| ≤
      64*t*Real.exp (-Real.pi/t) := by
  have hε := leftEpsilon_second_remainder ht htu
  have he : verticalA t-1/2-(2*t/Real.pi)*leftNome t =
      (t/Real.pi)*(leftEpsilon t-2*leftNome t) := by
    rw [leftEpsilon_eq_vertical_displacement]
    field_simp [ht.ne',Real.pi_ne_zero]
  have hscale : 0 ≤ t/Real.pi := (div_pos ht Real.pi_pos).le
  have hscale_le : t/Real.pi ≤ t := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  change |verticalA t-1/2-(2*t/Real.pi)*leftNome t| ≤ _
  rw [he,abs_mul,abs_of_nonneg hscale]
  calc
    _ ≤ (t/Real.pi)*(64*(leftNome t)^2) := mul_le_mul_of_nonneg_left hε hscale
    _ ≤ t*(64*(leftNome t)^2) := mul_le_mul_of_nonneg_right hscale_le (by positivity)
    _ = 64*t*Real.exp (-Real.pi/t) := by rw [leftNome_sq ht]; ring

theorem verticalA_left_remainder_isBigO :
    (fun t : ℝ => verticalA t-1/2-(2*t/Real.pi)*Real.exp (-Real.pi/(2*t)))
      =O[𝓝[>] (0 : ℝ)] (fun t => t*Real.exp (-Real.pi/t)) := by
  apply isBigO_iff.mpr
  refine ⟨64,?_⟩
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hu : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1/4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hu] with t ht htu
  simpa only [Real.norm_eq_abs,abs_of_pos (mul_pos ht (Real.exp_pos _)),mul_assoc]
    using verticalA_left_asymptotic_error_bound ht htu.le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.verticalA_left_remainder_isBigO
