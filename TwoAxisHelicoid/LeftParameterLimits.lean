import TwoAxisHelicoid.LeftComparisonLower
import TwoAxisHelicoid.LeftFluxDivergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
attribute [local irreducible] verticalA

theorem leftKappa0_tendsto_atTop :
    Tendsto leftKappa0 (𝓝[>] (0 : ℝ)) atTop := by
  have h := Tendsto.const_mul_atTop (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
  convert h using 1
  ext t
  unfold leftKappa0
  ring

theorem leftNome_eq_exp_neg_kappa0 (t : ℝ) : leftNome t = Real.exp (-leftKappa0 t) := by
  unfold leftNome leftKappa0
  congr 1
  ring

theorem leftNome_tendsto_zero :
    Tendsto leftNome (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa only [Function.comp_def,← leftNome_eq_exp_neg_kappa0] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp leftKappa0_tendsto_atTop

theorem leftEpsilon_tendsto_zero :
    Tendsto leftEpsilon (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [small_height_eventually_right] with t ht
    exact (leftEpsilon_bounds ht.1 ht.2).1.le
  · filter_upwards [small_height_eventually_right] with t ht
    exact (leftEpsilon_bounds ht.1 ht.2).2
  · simpa only [mul_zero] using leftNome_tendsto_zero.const_mul 6

theorem leftKappa_tendsto_atTop :
    Tendsto leftKappa (𝓝[>] (0 : ℝ)) atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [small_height_eventually_right,
    tendsto_atTop.mp leftKappa0_tendsto_atTop (b+1)] with t ht hlarge
  have hb := (leftKappa_bounds ht.1 ht.2).2.2
  linarith

theorem leftKappa_div_kappa0_tendsto_one :
    Tendsto (fun t : ℝ => leftKappa t/leftKappa0 t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hi := tendsto_inv_atTop_zero.comp leftKappa0_tendsto_atTop
  have he : Tendsto (fun t : ℝ => 1-leftEpsilon t*(leftKappa0 t)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def,mul_zero,sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (leftEpsilon_tendsto_zero.mul hi)
  apply he.congr'
  filter_upwards [small_height_eventually_right] with t ht
  have ht0 : 0 < t := ht.1
  have hk0 : leftKappa0 t ≠ 0 := ne_of_gt (div_pos Real.pi_pos (by positivity))
  rw [leftKappa_eq_kappa0_sub_epsilon]
  field_simp [hk0]

theorem leftNome_mul_exp_kappa (t : ℝ) :
    leftNome t*Real.exp (leftKappa t) = Real.exp (-leftEpsilon t) := by
  rw [leftNome_eq_exp_neg_kappa0,← Real.exp_add,leftKappa_eq_kappa0_sub_epsilon]
  congr 1
  ring

theorem leftChordH_mul_exp_kappa_tendsto_two :
    Tendsto (fun t : ℝ => leftChordH (leftNome t)*Real.exp (leftKappa t))
      (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  have he : ∀ t : ℝ, leftChordH (leftNome t)*Real.exp (leftKappa t) =
      (2/(1+(leftNome t)^2))*Real.exp (-leftEpsilon t) := by
    intro t
    rw [leftChordH]
    calc
      _ = (2/(1+(leftNome t)^2))*(leftNome t*Real.exp (leftKappa t)) := by ring
      _ = _ := by rw [leftNome_mul_exp_kappa]
  simp_rw [he]
  have hden : Tendsto (fun t : ℝ => 1+(leftNome t)^2) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [zero_pow (by decide : 2 ≠ 0),add_zero] using
      tendsto_const_nhds.add (leftNome_tendsto_zero.pow 2)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-leftEpsilon t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Function.comp_def,neg_zero,Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp
      leftEpsilon_tendsto_zero.neg
  simpa only [Pi.div_apply,div_one,mul_one] using
    (tendsto_const_nhds.div hden (by norm_num : (1 : ℝ) ≠ 0)).mul hexp

theorem leftKappa_pow_exp_tendsto_zero (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => (leftKappa t)^n*Real.exp (-c*leftKappa t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) c hc).comp
    leftKappa_tendsto_atTop
  simpa only [Function.comp_def,Real.rpow_natCast] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftChordH_mul_exp_kappa_tendsto_two
