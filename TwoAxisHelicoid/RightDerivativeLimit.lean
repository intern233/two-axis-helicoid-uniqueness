import TwoAxisHelicoid.WeightedPeriodContinuity
import TwoAxisHelicoid.MovingAbscissaSlope

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaHorizontalPeriod actualPeriodAlong thetaP verticalA

theorem periodK_branch_gap_ratio_limit :
    Tendsto (fun t : ℝ => periodK t (verticalA t)/(verticalA t-1))
      (𝓝[<] ellipticVerticalUpper) (𝓝 (2*(thetaP ellipticVerticalUpper 1).re)) := by
  have hc : ContinuousAt (fun p : ℝ × ℝ => 2*(thetaP p.1 p.2).re) (ellipticVerticalUpper,1) :=
    continuousAt_const.mul (thetaP_real_joint_continuousAt ellipticVerticalUpper_pos (by norm_num))
  simpa only [Complex.ofReal_one] using moving_abscissa_slope_limit
    (fun _ ht _ ha => periodK_a_hasDerivAt ht ha) (fun t _ => periodK_one t) hc

theorem horizontal_one_second_coefficient {t : ℝ} (ht : 0 < t) :
    2*(thetaP t 1).re*thetaHorizontalPeriod t 1-2*(thetaWeightedPeriod t 1).re = -2*ellipticI t ht := by
  let L := rhombicPeriodPair t ht
  have hz : (1:ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  have hi : (L.weierstrassP 1).im = 0 := rhombic_weierstrassP_real ht 1
  have he : 2*L.weierstrassP 1*fullComplexPeriod t 1-2*fullComplexWeight t ht 1 =
      -2*(L.g₂/12+2*L.weierstrassP 1*thetaEtaExpression t+L.weierstrassP 1^2) := by
    rw [fullComplexPeriod_one ht,fullComplexWeight_one ht]
    change 2*L.weierstrassP 1*(-thetaEtaExpression t-L.weierstrassP 1)-
      2*(L.g₂/12+L.weierstrassP 1*thetaEtaExpression t) = _
    ring
  rw [thetaP_eq_weierstrassP ht hz,thetaWeightedPeriod_eq_fullComplexWeight ht]
  have hr := congrArg Complex.re he
  simpa [ellipticI,L,Complex.mul_re,Complex.mul_im,hi,fullComplexPeriod_re] using hr

theorem horizontalPeriodDa_branch_gap_ratio_limit :
    Tendsto (fun t : ℝ => horizontalPeriodDa t (verticalA t)/(verticalA t-1))
      (𝓝[<] ellipticVerticalUpper) (𝓝 (-2*ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos)) := by
  have harg := (tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds verticalA_tendsto_one
  have hH := (horizontal_period_joint_continuousAt ellipticVerticalUpper_pos (by norm_num)).tendsto.comp harg
  have hW := Complex.continuous_re.continuousAt.tendsto.comp
    ((thetaWeightedPeriod_joint_continuousAt ellipticVerticalUpper_pos (by norm_num)).tendsto.comp harg)
  have hh := (periodK_branch_gap_ratio_limit.mul hH).sub ((tendsto_const_nhds (x := (2:ℝ))).mul hW)
  have he : (fun t : ℝ => periodK t (verticalA t)/(verticalA t-1)*thetaHorizontalPeriod t (verticalA t)-
      2*(thetaWeightedPeriod t (verticalA t)).re) =ᶠ[𝓝[<] ellipticVerticalUpper]
      fun t : ℝ => horizontalPeriodDa t (verticalA t)/(verticalA t-1) := by
    filter_upwards [verticalDomain_eventually_left] with t ht
    have ha := (verticalA_spec ht).1
    rw [horizontalPeriodDa_elliptic_formula ht.1 ⟨ha.1,by linarith [ha.2]⟩]
    field_simp [sub_ne_zero.mpr ha.2.ne]
  have hn := horizontal_one_second_coefficient ellipticVerticalUpper_pos
  convert hh.congr' he using 1
  exact congrArg (fun x : ℝ => 𝓝 x) hn.symm

theorem thetaGt_branch_right_limit :
    Tendsto (fun t : ℝ => (thetaGt t (verticalA t)).re) (𝓝[<] ellipticVerticalUpper)
      (𝓝 (ellipticC ellipticVerticalUpper ellipticVerticalUpper_pos/(2*Real.pi))) := by
  have he := (thetaG_real_t_hasDerivAt ellipticVerticalUpper_pos
    (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)).unique thetaG_one_t_hasDerivAt_upper
  have hc := Complex.continuous_re.continuousAt.comp
    (thetaGt_joint_continuousAt ellipticVerticalUpper_pos (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2))
  have harg := (tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds verticalA_tendsto_one
  simpa only [Function.comp_def,id_eq,he] using hc.tendsto.comp harg

theorem actualPeriodAlong_deriv_right_limit :
    Tendsto (deriv actualPeriodAlong) (𝓝[<] ellipticVerticalUpper)
      (𝓝 (-deriv ellipticFReal ellipticVerticalUpper+
        ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos/Real.pi)) := by
  have hnh : horizontalDomain ∈ 𝓝 (ellipticVerticalUpper,1) :=
    horizontalDomain_isOpen.mem_nhds ⟨ellipticVerticalUpper_pos,by norm_num⟩
  have harg := (tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds verticalA_tendsto_one
  have hHt := (horizontal_period_and_partials_continuousOn.2.2.continuousAt hnh).tendsto.comp harg
  rw [horizontalPeriodDt_one ellipticVerticalUpper_pos] at hHt
  have hcpos := ellipticC_pos ellipticVerticalUpper_pos
  have hrat := horizontalPeriodDa_branch_gap_ratio_limit.div thetaGa_branch_gap_ratio_limit hcpos.ne'
  have hh := hHt.sub (thetaGt_branch_right_limit.mul hrat)
  have he : (fun t : ℝ => horizontalPeriodDt t (verticalA t)-(thetaGt t (verticalA t)).re*
      ((horizontalPeriodDa t (verticalA t)/(verticalA t-1))/((thetaGa t (verticalA t)).re/(verticalA t-1)))) =ᶠ[𝓝[<] ellipticVerticalUpper]
      deriv actualPeriodAlong := by
    filter_upwards [verticalDomain_eventually_left] with t ht
    have ha := (verticalA_spec ht).1
    have hgn := (thetaGa_re_neg_unit ht.1 ha.1 ha.2).ne
    rw [(actualPeriodAlong_hasDerivAt ht).deriv,(verticalA_hasDerivAt ht).deriv]
    field_simp [hgn,sub_ne_zero.mpr ha.2.ne]
    ring
  convert hh.congr' he using 1
  congr 1
  field_simp [hcpos.ne',Real.pi_ne_zero]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_deriv_right_limit
