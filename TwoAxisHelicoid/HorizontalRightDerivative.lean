import TwoAxisHelicoid.HorizontalSecondOrder
import TwoAxisHelicoid.VerticalSquareLimit
import TwoAxisHelicoid.FullPeriodBranch
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
attribute [local irreducible] thetaHorizontalPeriod actualPeriodAlong verticalA

theorem horizontal_second_deriv_one {t : ℝ} (ht : 0 < t) :
    deriv (deriv (thetaHorizontalPeriod t)) 1 = -2*ellipticI t ht := by
  have he : deriv (thetaHorizontalPeriod t) =ᶠ[𝓝 (1:ℝ)] horizontalPeriodDa t := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)] with a ha
    exact (horizontal_period_a_hasDerivAt ht ha).deriv
  rw [he.deriv_eq,(horizontalPeriodDa_hasDerivAt_one ht).deriv]

theorem horizontal_right_a_mean_exists {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    ∃ c ∈ Ioo (verticalA t) 1,
      thetaHorizontalPeriod ellipticVerticalUpper (verticalA t)-thetaHorizontalPeriod ellipticVerticalUpper 1 =
        deriv (deriv (thetaHorizontalPeriod ellipticVerticalUpper)) c/2*(1-verticalA t)^2 := by
  have ha := (verticalA_spec ht).1
  have hunit (x : ℝ) (hx : x ∈ Icc (verticalA t) 1) : x ∈ Ioo (0:ℝ) 2 :=
    ⟨ha.1.trans_le hx.1,by linarith [hx.2]⟩
  have h1 : deriv (thetaHorizontalPeriod ellipticVerticalUpper) 1 = 0 := by
    rw [(horizontal_period_a_hasDerivAt ellipticVerticalUpper_pos (by norm_num : (1:ℝ) ∈ Ioo 0 2)).deriv,
      horizontal_period_da_at_one ellipticVerticalUpper_pos]
  obtain ⟨c,hc,he⟩ := exists_second_order_mean ha.2
    (fun x hx => (horizontal_period_a_analyticAt ellipticVerticalUpper_pos (hunit x hx)).differentiableAt.hasDerivAt)
    (fun x hx => (horizontal_period_a_analyticAt ellipticVerticalUpper_pos (hunit x hx)).deriv.differentiableAt.hasDerivAt) h1
  exact ⟨c,hc,by linear_combination he⟩

noncomputable def horizontalRightAMean (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper then (horizontal_right_a_mean_exists ht).choose else 1

theorem horizontalRightAMean_spec {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    horizontalRightAMean t ∈ Ioo (verticalA t) 1 ∧
      thetaHorizontalPeriod ellipticVerticalUpper (verticalA t)-thetaHorizontalPeriod ellipticVerticalUpper 1 =
        deriv (deriv (thetaHorizontalPeriod ellipticVerticalUpper)) (horizontalRightAMean t)/2*(1-verticalA t)^2 := by
  simpa only [horizontalRightAMean,dite_eq_left ht] using (horizontal_right_a_mean_exists ht).choose_spec

theorem horizontalRightAMean_tendsto_one :
    Tendsto horizontalRightAMean (𝓝[<] ellipticVerticalUpper) (𝓝 1) := by
  apply verticalA_tendsto_one.squeeze' tendsto_const_nhds
  · filter_upwards [verticalDomain_eventually_left] with t ht
    exact (horizontalRightAMean_spec ht).1.1.le
  · filter_upwards [verticalDomain_eventually_left] with t ht
    exact (horizontalRightAMean_spec ht).1.2.le

theorem horizontal_right_a_difference_limit :
    Tendsto (fun t : ℝ => (thetaHorizontalPeriod ellipticVerticalUpper (verticalA t)-
      thetaHorizontalPeriod ellipticVerticalUpper 1)/(t-ellipticVerticalUpper))
      (𝓝[<] ellipticVerticalUpper) (𝓝 (ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos/Real.pi)) := by
  let T := ellipticVerticalUpper
  have hc := (horizontal_period_a_analyticAt ellipticVerticalUpper_pos
    (by norm_num : (1:ℝ) ∈ Ioo 0 2)).deriv.deriv.continuousAt.tendsto.comp horizontalRightAMean_tendsto_one
  rw [horizontal_second_deriv_one ellipticVerticalUpper_pos] at hc
  have hs := verticalA_square_gap_limit.neg
  have hh := (hc.div_const 2).mul hs
  have he : (fun t : ℝ => deriv (deriv (thetaHorizontalPeriod T)) (horizontalRightAMean t)/2*
      (-((1-verticalA t)^2/(T-t)))) =ᶠ[𝓝[<] T]
      fun t : ℝ => (thetaHorizontalPeriod T (verticalA t)-thetaHorizontalPeriod T 1)/(t-T) := by
    filter_upwards [verticalDomain_eventually_left] with t ht
    rw [(horizontalRightAMean_spec ht).2]
    rw [show t-T = -(T-t) by ring,div_neg]
    dsimp only [T]
    ring
  convert hh.congr' he using 1
  congr 1
  ring

theorem horizontal_right_t_mean_exists {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    ∃ s ∈ Ioo t ellipticVerticalUpper,
      horizontalPeriodDt s (verticalA t) =
        (thetaHorizontalPeriod t (verticalA t)-thetaHorizontalPeriod ellipticVerticalUpper (verticalA t))/(t-ellipticVerticalUpper) := by
  have ha : verticalA t ∈ Ioo (0:ℝ) 2 := ⟨(verticalA_spec ht).1.1,by linarith [(verticalA_spec ht).1.2]⟩
  obtain ⟨s,hs,he⟩ := exists_hasDerivAt_eq_slope
    (fun u : ℝ => thetaHorizontalPeriod u (verticalA t))
    (fun u : ℝ => horizontalPeriodDt u (verticalA t)) ht.2
    (fun u hu => (horizontal_period_t_hasDerivAt (ht.1.trans_le hu.1) ha).continuousAt.continuousWithinAt)
    (fun u hu => horizontal_period_t_hasDerivAt (ht.1.trans hu.1) ha)
  refine ⟨s,hs,?_⟩
  rw [he]
  rw [← neg_sub (thetaHorizontalPeriod t (verticalA t)),← neg_sub t ellipticVerticalUpper,neg_div_neg_eq]

noncomputable def horizontalRightTMean (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper then (horizontal_right_t_mean_exists ht).choose else ellipticVerticalUpper

theorem horizontalRightTMean_spec {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    horizontalRightTMean t ∈ Ioo t ellipticVerticalUpper ∧
      horizontalPeriodDt (horizontalRightTMean t) (verticalA t) =
        (thetaHorizontalPeriod t (verticalA t)-thetaHorizontalPeriod ellipticVerticalUpper (verticalA t))/(t-ellipticVerticalUpper) := by
  simpa only [horizontalRightTMean,dite_eq_left ht] using (horizontal_right_t_mean_exists ht).choose_spec

theorem horizontalRightTMean_tendsto_upper :
    Tendsto horizontalRightTMean (𝓝[<] ellipticVerticalUpper) (𝓝 ellipticVerticalUpper) := by
  apply (tendsto_id'.mpr nhdsWithin_le_nhds).squeeze' tendsto_const_nhds
  · filter_upwards [verticalDomain_eventually_left] with t ht
    exact (horizontalRightTMean_spec ht).1.1.le
  · filter_upwards [verticalDomain_eventually_left] with t ht
    exact (horizontalRightTMean_spec ht).1.2.le

theorem horizontalPeriodDt_one {t : ℝ} (ht : 0 < t) :
    horizontalPeriodDt t 1 = -deriv ellipticFReal t := by
  have he : (fun s : ℝ => thetaHorizontalPeriod s 1) =ᶠ[𝓝 t] fun s => -ellipticFReal s := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact thetaHorizontalPeriod_one hs
  exact (horizontal_period_t_hasDerivAt ht (by norm_num : (1:ℝ) ∈ Ioo 0 2)).unique
    ((ellipticFReal_differentiableAt ht).hasDerivAt.neg.congr_of_eventuallyEq he)

theorem horizontal_right_t_difference_limit :
    Tendsto (fun t : ℝ => (thetaHorizontalPeriod t (verticalA t)-
      thetaHorizontalPeriod ellipticVerticalUpper (verticalA t))/(t-ellipticVerticalUpper))
      (𝓝[<] ellipticVerticalUpper) (𝓝 (-deriv ellipticFReal ellipticVerticalUpper)) := by
  have hnh : horizontalDomain ∈ 𝓝 (ellipticVerticalUpper,1) :=
    horizontalDomain_isOpen.mem_nhds ⟨ellipticVerticalUpper_pos,by norm_num⟩
  have hc := (horizontal_period_and_partials_continuousOn.2.2.continuousAt hnh).tendsto.comp
    (horizontalRightTMean_tendsto_upper.prodMk_nhds verticalA_tendsto_one)
  rw [horizontalPeriodDt_one ellipticVerticalUpper_pos] at hc
  apply hc.congr'
  filter_upwards [verticalDomain_eventually_left] with t ht
  exact (horizontalRightTMean_spec ht).2

theorem actualPeriodAlong_right_slope :
    Tendsto (fun t : ℝ => (actualPeriodAlong t+Real.pi/ellipticVerticalUpper)/(t-ellipticVerticalUpper))
      (𝓝[<] ellipticVerticalUpper)
      (𝓝 (-deriv ellipticFReal ellipticVerticalUpper+ellipticI ellipticVerticalUpper ellipticVerticalUpper_pos/Real.pi)) := by
  have hh := horizontal_right_t_difference_limit.add horizontal_right_a_difference_limit
  convert hh using 1
  funext t
  rw [← add_div,sub_add_sub_cancel,thetaHorizontalPeriod_right_endpoint]
  unfold actualPeriodAlong
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_right_slope
