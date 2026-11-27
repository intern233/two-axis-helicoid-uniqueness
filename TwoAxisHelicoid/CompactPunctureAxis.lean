import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.Topology

namespace TwoAxisHelicoid
open Set

/-- A complete unbounded coordinate line in a once-punctured compact space
accumulates at its puncture. -/
theorem puncture_mem_closure_unbounded_axis {M : Type*} [TopologicalSpace M] [CompactSpace M]
    {p : M} {u : M → ℝ} (hu : ∀ q ≠ p, ContinuousAt u q)
    {γ : ℝ → M} (hcoordinate : ∀ r, u (γ r) = r) :
    p ∈ closure (range γ) := by
  by_contra hp
  have hcont : ContinuousOn u (closure (range γ)) := by
    intro q hq
    exact (hu q (by rintro rfl; exact hp hq)).continuousWithinAt
  have hcompact : IsCompact (closure (range γ)) := isClosed_closure.isCompact
  obtain ⟨B,hB⟩ := hcompact.bddAbove_image hcont
  have h := hB (mem_image_of_mem u (subset_closure (mem_range_self (B+1))))
  rw [hcoordinate] at h
  linarith

/-- If the fixed set off the puncture is exactly a complete coordinate axis,
its compactification is connected. -/
theorem compact_fixed_locus_connected_of_axis {M : Type*} [TopologicalSpace M]
    [CompactSpace M] [T2Space M] {p : M} {f : M → M} (hf : Continuous f)
    {u : M → ℝ} (hu : ∀ q ≠ p, ContinuousAt u q)
    {γ : ℝ → M} (hγ : Continuous γ) (hcoordinate : ∀ r, u (γ r) = r)
    (hγfixed : ∀ r, f (γ r) = γ r)
    (hfixed : ∀ q ≠ p, f q = q → q ∈ range γ) :
    IsConnected {q : M | f q = q} := by
  have hp := puncture_mem_closure_unbounded_axis hu hcoordinate
  have hsub : closure (range γ) ⊆ {q : M | f q = q} :=
    closure_minimal (by rintro q ⟨r,rfl⟩; exact hγfixed r) (isClosed_eq hf continuous_id)
  have he : {q : M | f q = q} = closure (range γ) := by
    apply Set.Subset.antisymm
    · intro q hq
      by_cases hqp : q = p
      · simpa [hqp] using hp
      · exact subset_closure (hfixed q hqp hq)
    · exact hsub
  rw [he]
  exact (isConnected_range hγ).closure

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_fixed_locus_connected_of_axis
