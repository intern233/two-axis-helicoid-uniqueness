import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Connected.Clopen

namespace TwoAxisHelicoid
open Set

theorem proper_local_homeomorph_finite_fibers {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [T2Space E] {f : E → X}
    (hp : IsProperMap f) (hl : IsLocalHomeomorph f) (x : X) :
    (f ⁻¹' {x}).Finite := by
  apply (hp.isCompact_preimage isCompact_singleton).finite
  apply IsDiscrete.of_openPartialHomeomorph f subset_rfl
  intro e _
  obtain ⟨φ,he,hφ⟩ := hl e
  exact ⟨φ,he,hφ.symm⟩

/-- A proper local homeomorphism is a covering with finite fibers. This
supplies the topological covering step once the geometric projection has
been proved proper and locally invertible. -/
theorem proper_local_homeomorph_isCoveringMap {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [T2Space E] {f : E → X}
    (hp : IsProperMap f) (hl : IsLocalHomeomorph f) : IsCoveringMap f := by
  intro x
  apply hp.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
    (proper_local_homeomorph_finite_fibers hp hl x)
  intro e _
  obtain ⟨φ,he,hφ⟩ := hl e
  exact ⟨φ,he,hφ.symm⟩

theorem proper_local_homeomorph_surjective {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [PreconnectedSpace X] [Nonempty E]
    {f : E → X} (hp : IsProperMap f) (hl : IsLocalHomeomorph f) : Function.Surjective f := by
  have hc : IsClopen (range f) := ⟨hp.isClosedMap.isClosed_range,hl.isOpenMap.isOpen_range⟩
  exact range_eq_univ.mp (hc.eq_univ (range_nonempty f))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.proper_local_homeomorph_isCoveringMap
