import TwoAxisHelicoid.AllHorizontalDerivative
import TwoAxisHelicoid.VerticalBranchDerivative
import TwoAxisHelicoid.HorizontalRightValue
import TwoAxisHelicoid.ScalarBivariateDerivative

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
attribute [local irreducible] thetaHorizontalPeriod

noncomputable def actualPeriodAlong (t : ℝ) : ℝ := thetaHorizontalPeriod t (verticalA t)

theorem actualPeriodAlong_hasDerivAt {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    HasDerivAt actualPeriodAlong
      (horizontalPeriodDt t (verticalA t)+deriv verticalA t*horizontalPeriodDa t (verticalA t)) t := by
  have ha := (verticalA_spec ht).1
  have ha2 : verticalA t ∈ Ioo (0:ℝ) 2 := ⟨ha.1,by linarith [ha.2]⟩
  have hnh : horizontalDomain ∈ 𝓝 (t,verticalA t) := horizontalDomain_isOpen.mem_nhds ⟨ht.1,ha2⟩
  have hdt : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,verticalA t),
      HasDerivAt (fun s => thetaHorizontalPeriod s p.2) (horizontalPeriodDt p.1 p.2) p.1 := by
    filter_upwards [hnh] with p hp
    exact horizontal_period_t_hasDerivAt hp.1 hp.2
  have hda : ∀ᶠ p : ℝ × ℝ in 𝓝 (t,verticalA t),
      HasDerivAt (thetaHorizontalPeriod p.1) (horizontalPeriodDa p.1 p.2) p.2 := by
    filter_upwards [hnh] with p hp
    exact horizontal_period_a_hasDerivAt hp.1 hp.2
  have hd := scalar_bivariate_curve_hasDerivAt hdt hda
    (horizontal_period_and_partials_continuousOn.2.2.continuousAt hnh)
    (horizontal_period_and_partials_continuousOn.2.1.continuousAt hnh)
    (hasDerivAt_id t) (verticalA_hasDerivAt ht).differentiableAt.hasDerivAt
  unfold actualPeriodAlong
  simpa only [id_eq,one_mul] using hd

theorem actualPeriodAlong_continuousOn : ContinuousOn actualPeriodAlong (Ioo (0:ℝ) ellipticVerticalUpper) :=
  fun _ ht => (actualPeriodAlong_hasDerivAt ht).continuousAt.continuousWithinAt

theorem actualPeriodAlong_deriv_continuousAt {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    ContinuousAt (deriv actualPeriodAlong) t := by
  have ha := (verticalA_spec ht).1
  have hnh : horizontalDomain ∈ 𝓝 (t,verticalA t) :=
    horizontalDomain_isOpen.mem_nhds ⟨ht.1,ha.1,by linarith [ha.2]⟩
  have hp : ContinuousAt (fun s : ℝ => (s,verticalA s)) t :=
    continuousAt_id.prodMk (verticalA_continuousAt ht)
  have hct := (horizontal_period_and_partials_continuousOn.2.2.continuousAt hnh).comp
    (f := fun s : ℝ => (s,verticalA s)) hp
  have hca := (horizontal_period_and_partials_continuousOn.2.1.continuousAt hnh).comp
    (f := fun s : ℝ => (s,verticalA s)) hp
  have hc := hct.add ((verticalA_deriv_continuousAt ht).mul hca)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact (actualPeriodAlong_hasDerivAt hs).deriv

theorem actualPeriodAlong_tendsto_right :
    Tendsto actualPeriodAlong (𝓝[<] ellipticVerticalUpper) (𝓝 (-Real.pi/ellipticVerticalUpper)) := by
  have hp := horizontal_period_joint_continuousAt ellipticVerticalUpper_pos
    (by norm_num : (1:ℝ) ∈ Ioo 0 2)
  have hid : Tendsto (fun s : ℝ => s) (𝓝[<] ellipticVerticalUpper) (𝓝 ellipticVerticalUpper) :=
    tendsto_id'.mpr nhdsWithin_le_nhds
  have h := hp.tendsto.comp (hid.prodMk_nhds verticalA_tendsto_one)
  unfold actualPeriodAlong
  simpa only [Function.comp_def,thetaHorizontalPeriod_right_endpoint] using h

theorem actualPeriodAlong_eventually_negative_right :
    ∀ᶠ t in 𝓝[<] ellipticVerticalUpper, actualPeriodAlong t < 0 :=
  actualPeriodAlong_tendsto_right.eventually (eventually_lt_nhds
    (div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ellipticVerticalUpper_pos))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_hasDerivAt
#print axioms TwoAxisHelicoid.actualPeriodAlong_eventually_negative_right
