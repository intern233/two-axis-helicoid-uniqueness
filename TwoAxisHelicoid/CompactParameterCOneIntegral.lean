import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Group.Bounded

namespace TwoAxisHelicoid
open Set Filter Metric MeasureTheory
open scoped Topology Interval ContDiff

/-- Integrating a jointly C¹ function over a fixed compact interval
preserves C¹ regularity in a Euclidean parameter. Local domination
is obtained from a compact ball in the parameter and the interval. -/
theorem contDiff_one_compact_parameter_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {F : E × ℝ → G} (sm : ContDiff ℝ 1 F) (a b : ℝ) :
    ContDiff ℝ 1 (fun x : E => ∫ t in a..b, F (x,t)) := by
  let D := fun p : E × ℝ => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have cd : Continuous D := (sm.continuous_fderiv one_ne_zero).clm_comp continuous_const
  have sec (x : E) : Continuous (fun t : ℝ => F (x,t)) := sm.continuous.comp (continuous_const.prodMk continuous_id)
  have secD (x : E) : Continuous (fun t : ℝ => D (x,t)) := cd.comp (continuous_const.prodMk continuous_id)
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => ∫ t in a..b, D (x,t),
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' cd a b,?_⟩
  intro x
  obtain ⟨M,bound⟩ := ((isCompact_closedBall x 1).prod isCompact_uIcc).exists_bound_of_continuousOn cd.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le'' (F:=fun y t => F (y,t))
    (F':=fun y t => D (y,t)) (bound:=fun _ => M) (ball_mem_nhds x zero_lt_one)
  · exact .of_forall (fun y => (sec y).aestronglyMeasurable)
  · exact (sec x).intervalIntegrable a b
  · exact (secD x).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_uIoc (a:=a) (b:=b))] with t ht
    intro y hy
    exact bound (y,t) ⟨ball_subset_closedBall hy,uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact .of_forall (fun t y _ => ((sm.differentiable one_ne_zero (y,t)).hasFDerivAt).comp y
      (hasFDerivAt_prodMk_left y t))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.contDiff_one_compact_parameter_integral
