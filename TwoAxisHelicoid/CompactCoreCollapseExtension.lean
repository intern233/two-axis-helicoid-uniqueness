import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Separation.Hausdorff

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

/-- A map on an open embedded core that is constant outside a compact set
extends to the ambient surface, taking the same constant everywhere off
the image of the core. -/
theorem extend_map_from_open_core {U M T : Type*} [TopologicalSpace U] [TopologicalSpace M]
    [T2Space M] [TopologicalSpace T] {e : U → M} (he : IsOpenEmbedding e)
    (f : C(U,T)) (p : T) {K : Set U} (hK : IsCompact K) (hf : ∀ x ∉ K, f x = p) :
    ∃ F : C(M,T), (∀ x, F (e x) = f x) ∧ ∀ y ∉ e '' K, F y = p := by
  classical
  let F := Function.extend e f (fun _ => p)
  have h₁ (x : U) : F (e x) = f x := he.injective.extend_apply ..
  have h₂ (y : M) (hy : y ∉ e '' K) : F y = p := by
    by_cases hy' : y ∈ range e
    · obtain ⟨x,rfl⟩ := hy'
      exact (h₁ x).trans (hf x (fun h => hy ⟨x,h,rfl⟩))
    · exact Function.extend_apply' _ _ _ hy'
  have hclosed := (hK.image he.continuous).isClosed
  have hcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro y
    by_cases hy : y ∈ range e
    · obtain ⟨x,rfl⟩ := hy
      apply he.continuousAt_iff.mp
      have h : F ∘ e = f := funext h₁
      rw [h]
      exact f.continuous.continuousAt
    · have hn : y ∉ e '' K := fun h => hy (image_subset_range _ _ h)
      apply (continuousAt_const (y := p)).congr_of_eventuallyEq
      filter_upwards [hclosed.isOpen_compl.mem_nhds hn] with z hz
      exact h₂ z hz
  exact ⟨⟨F,hcont⟩,h₁,h₂⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.extend_map_from_open_core
