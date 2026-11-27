import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Asymptotics.Lemmas

namespace TwoAxisHelicoid
open Filter Asymptotics
open scoped Topology

theorem analytic_quadratic_remainder {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a) :
    (fun t => f t-f a-deriv f a*(t-a)) =O[𝓝 a] (fun t => (t-a)^2) := by
  have hh := hf.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 2
  have ht : Tendsto (fun t : ℝ => t-a) (𝓝 a) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => t-a) a := continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using hc.tendsto
  have hc := hh.comp_tendsto ht
  simpa [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,
    FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,sub_sub,abs_sq,Function.comp_def,mul_comm] using hc

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_quadratic_remainder
