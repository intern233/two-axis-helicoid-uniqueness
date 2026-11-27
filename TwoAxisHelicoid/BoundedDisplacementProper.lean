import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace

namespace TwoAxisHelicoid
open Set Metric

/-- A continuous map which moves each point a uniformly bounded distance
in a proper normed space is proper. -/
theorem bounded_displacement_isProperMap {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f : E → E} (hf : Continuous f) {B : ℝ} (hB : ∀ x, ‖x-f x‖ ≤ B) : IsProperMap f := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨hf,?_⟩
  intro K hK
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  apply (isCompact_closedBall (0 : E) (B+R)).of_isClosed_subset (hK.isClosed.preimage hf)
  intro x hx
  rw [mem_closedBall,dist_zero_right]
  calc
    ‖x‖ = ‖(x-f x)+f x‖ := by rw [sub_add_cancel]
    _ ≤ ‖x-f x‖+‖f x‖ := norm_add_le _ _
    _ ≤ B+R := add_le_add (hB x) (hR _ hx)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.bounded_displacement_isProperMap
