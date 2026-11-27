import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.ProperSpace

namespace TwoAxisHelicoid
open Set Metric

theorem continuous_compact_uniform_small_parameter
    {E P F : Type*} [MetricSpace E] [NormedAddCommGroup P] [ProperSpace P]
    [MetricSpace F] {H : E × P → F} (hH : Continuous H) {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ w : P, ‖w‖ ≤ δ → dist (H (x,w)) (H (x,0)) ≤ ε := by
  have hc := (hK.prod (isCompact_closedBall (0 : P) 1)).uniformContinuousOn_of_continuous hH.continuousOn
  obtain ⟨η,hη,hηbound⟩ := Metric.uniformContinuousOn_iff_le.mp hc ε hε
  refine ⟨min 1 η,lt_min (by norm_num) hη,?_⟩
  intro x hx w hw
  apply hηbound (x,w) ⟨hx,?_⟩ (x,0) ⟨hx,?_⟩ ?_
  · simpa only [mem_closedBall,dist_zero_right] using hw.trans (min_le_left _ _)
  · simp
  · simpa only [Prod.dist_eq,dist_self,dist_zero_right,max_eq_right (norm_nonneg w)] using
      hw.trans (min_le_right _ _)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.continuous_compact_uniform_small_parameter
