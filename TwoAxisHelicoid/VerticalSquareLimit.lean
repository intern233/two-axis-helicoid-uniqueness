import TwoAxisHelicoid.VerticalSecondOrder

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaG thetaLogFourth verticalA

noncomputable def verticalMeanPoint (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper then (vertical_root_second_order_mean ht).choose else 1

theorem verticalMeanPoint_spec {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    verticalMeanPoint t ∈ Ioo (verticalA t) 1 ∧
      -(thetaG t 1).re = (thetaLogFourth t (verticalMeanPoint t)).re / 2 * (1-verticalA t)^2 := by
  simpa only [verticalMeanPoint,dite_eq_left ht] using (vertical_root_second_order_mean ht).choose_spec

theorem verticalDomain_eventually_left :
    ∀ᶠ t in 𝓝[<] ellipticVerticalUpper, t ∈ Ioo (0:ℝ) ellipticVerticalUpper :=
  ((eventually_gt_nhds ellipticVerticalUpper_pos).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin

theorem verticalMeanPoint_tendsto_one :
    Tendsto verticalMeanPoint (𝓝[<] ellipticVerticalUpper) (𝓝 1) := by
  apply verticalA_tendsto_one.squeeze' tendsto_const_nhds
  · filter_upwards [verticalDomain_eventually_left] with t ht
    exact (verticalMeanPoint_spec ht).1.1.le
  · filter_upwards [verticalDomain_eventually_left] with t ht
    exact (verticalMeanPoint_spec ht).1.2.le

theorem verticalA_square_gap_limit :
    Tendsto (fun t : ℝ => (1-verticalA t)^2/(ellipticVerticalUpper-t))
      (𝓝[<] ellipticVerticalUpper) (𝓝 (1/Real.pi)) := by
  let T := ellipticVerticalUpper
  let C := fun t : ℝ => (thetaLogFourth t (verticalMeanPoint t)).re
  have hC : Tendsto C (𝓝[<] T) (𝓝 (ellipticC T ellipticVerticalUpper_pos)) := by
    have hj := thetaLogFourth_real_joint_continuousAt ellipticVerticalUpper_pos
      (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)
    have harg : Tendsto (fun t : ℝ => (t,verticalMeanPoint t)) (𝓝[<] T) (𝓝 (T,1)) :=
      tendsto_id'.mpr nhdsWithin_le_nhds |>.prodMk_nhds verticalMeanPoint_tendsto_one
    simpa only [Function.comp_def,Complex.ofReal_one,thetaLogFourth_one_re ellipticVerticalUpper_pos] using hj.tendsto.comp harg
  have hs : Tendsto (fun t : ℝ => (thetaG t 1).re/(t-T)) (𝓝[<] T)
      (𝓝 (ellipticC T ellipticVerticalUpper_pos/(2*Real.pi))) := by
    have hd := thetaG_one_t_hasDerivAt_upper.tendsto_slope.mono_left
      (nhdsLT_le_nhdsNE ellipticVerticalUpper)
    simpa only [slope_fun_def_field,thetaG_vertical_upper_one_zero,Complex.zero_re,sub_zero] using hd
  have hcpos : 0 < ellipticC T ellipticVerticalUpper_pos := ellipticC_pos ellipticVerticalUpper_pos
  have hlim := ((tendsto_const_nhds (x := (2:ℝ))).mul hs).div hC hcpos.ne'
  have he : (fun t : ℝ => 2*((thetaG t 1).re/(t-T))/C t) =ᶠ[𝓝[<] T]
      fun t : ℝ => (1-verticalA t)^2/(T-t) := by
    filter_upwards [verticalDomain_eventually_left,hC.eventually (eventually_gt_nhds hcpos)] with t ht hct
    have hm := (verticalMeanPoint_spec ht).2
    have htn : T-t ≠ 0 := (sub_pos.mpr ht.2).ne'
    have hnt : t-T ≠ 0 := sub_ne_zero.mpr ht.2.ne
    change - (thetaG t 1).re = C t / 2 * (1-verticalA t)^2 at hm
    field_simp [hct.ne',htn,hnt]
    linear_combination -2*(T-t)*hm
  convert hlim.congr' he using 1
  congr 1
  field_simp [hcpos.ne',Real.pi_ne_zero]

theorem verticalA_sqrt_gap_limit :
    Tendsto (fun t : ℝ => (1-verticalA t)/Real.sqrt (ellipticVerticalUpper-t))
      (𝓝[<] ellipticVerticalUpper) (𝓝 (1/Real.sqrt Real.pi)) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp verticalA_square_gap_limit
  have he : (fun t : ℝ => Real.sqrt ((1-verticalA t)^2/(ellipticVerticalUpper-t))) =ᶠ[𝓝[<] ellipticVerticalUpper]
      fun t : ℝ => (1-verticalA t)/Real.sqrt (ellipticVerticalUpper-t) := by
    filter_upwards [verticalDomain_eventually_left] with t ht
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos (sub_pos.mpr (verticalA_spec ht).1.2)]
  simpa only [Function.comp_def,Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1),Real.sqrt_one] using hs.congr' he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.verticalA_square_gap_limit
#print axioms TwoAxisHelicoid.verticalA_sqrt_gap_limit
