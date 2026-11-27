import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.EMetricSpace.Basic

namespace TwoAxisHelicoid
open Set Filter Metric

/-- A proper map to a proper metric space proves completeness of a source
extended metric whenever ambient distances are bounded by source distances.
This will apply to an immersion with its induced length metric. -/
theorem completeSpace_of_proper_distance_decreasing
    {M E : Type*} [EMetricSpace M] [MetricSpace E] [ProperSpace E]
    {X : M → E} (hproper : IsProperMap X)
    (hle : ∀ x y, edist (X x) (X y) ≤ edist x y) : CompleteSpace M := by
  constructor
  intro f hf
  obtain ⟨s,hs,hdiam⟩ := (EMetric.cauchy_iff.mp hf).2 1 zero_lt_one
  obtain ⟨x,hx⟩ := hf.1.nonempty_of_mem hs
  have hmem : X ⁻¹' closedBall (X x) 1 ∈ f := by
    apply mem_of_superset hs
    intro y hy
    apply (edist_le_ofReal (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa only [ENNReal.ofReal_one] using (hle y x).trans (hdiam y hy x hx).le
  obtain ⟨y,_hy,ht⟩ := (hproper.isCompact_preimage (isCompact_closedBall (X x) 1)).isComplete
    f hf (le_principal_iff.mpr hmem)
  exact ⟨y,ht⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.completeSpace_of_proper_distance_decreasing
