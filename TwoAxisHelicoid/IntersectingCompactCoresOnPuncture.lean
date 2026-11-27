module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Hausdorff

public section

namespace TwoAxisHelicoid
open Set Topology
open scoped Topology

/-- Suppose two open copies of a fixed connected patch always meet in the compact
ambient space. If its closure avoids the puncture, a compact connected set containing
any prescribed point of the punctured space also meets each homeomorphic image of itself. -/
theorem intersecting_compact_cores_on_puncture {T M : Type*} [TopologicalSpace T]
    [CompactSpace T] [T1Space T] [TopologicalSpace M] [T2Space M] [PathConnectedSpace M]
    (point : T) (mark : M ≃ₜ {z : T // z ≠ point}) (C : Set T) [ConnectedSpace C]
    (opened : IsOpen C) (avoids : point ∉ closure C) (base : C)
    (meet_images : ∀ f g : C → T, IsOpenEmbedding f → IsOpenEmbedding g →
      ¬ Disjoint (range f) (range g)) (p : M) :
    ∃ K : Set M, IsCompact K ∧ IsConnected K ∧ p ∈ K ∧
      ∀ d : M ≃ₜ M, ∃ a ∈ K, d a ∈ K := by
  classical
  let U := {z : {z : T // z ≠ point} | z.1 ∈ closure C}
  have image : Subtype.val '' U = closure C := by
    ext z
    refine ⟨fun ⟨y,hy,e⟩ => e ▸ hy, fun hz => ?_⟩
    exact ⟨⟨z,fun eq => avoids (eq ▸ hz)⟩,hz,rfl⟩
  have compact : IsCompact U := Subtype.isCompact_iff.mpr (image ▸ isClosed_closure.isCompact)
  let i (z : C) : {z : T // z ≠ point} :=
    ⟨z.1,fun eq => avoids (eq ▸ subset_closure z.2)⟩
  have op : IsOpen {z : T | z ≠ point} := isClosed_singleton.isOpen_compl
  have oi : IsOpenEmbedding i := (IsOpenEmbedding.of_comp_iff i op.isOpenEmbedding_subtypeVal).mp
    opened.isOpenEmbedding_subtypeVal
  let f := mark.symm ∘ i
  have of' : IsOpenEmbedding f := mark.symm.isOpenEmbedding.comp oi
  let j := (Subtype.val : {z : T // z ≠ point} → T) ∘ mark
  have oj : IsOpenEmbedding j := op.isOpenEmbedding_subtypeVal.comp mark.isOpenEmbedding
  let V := closure (range f)
  have inc : range f ⊆ mark.symm '' U := by
    rintro _ ⟨x,rfl⟩
    exact ⟨i x,subset_closure x.2,rfl⟩
  have cU := compact.image mark.symm.continuous
  have cV : IsCompact V := cU.of_isClosed_subset isClosed_closure (closure_minimal inc cU.isClosed)
  let γ := PathConnectedSpace.somePath (f base) p
  have bV : f base ∈ V := subset_closure (mem_range_self base)
  refine ⟨V ∪ range γ,cV.union (isCompact_range γ.continuous),?_,Or.inr ⟨1,γ.target⟩,?_⟩
  · exact IsConnected.union ⟨f base,bV,0,γ.source⟩ (isConnected_range of'.continuous).closure
      (isConnected_range γ.continuous)
  · intro d
    have meet := meet_images (j ∘ f) (j ∘ d ∘ f)
      (oj.comp of') (oj.comp (d.isOpenEmbedding.comp of'))
    obtain ⟨_,⟨x,rfl⟩,⟨y,eq⟩⟩ := Set.not_disjoint_iff.mp meet
    have e : d (f y) = f x := oj.injective eq
    refine ⟨f y,Or.inl (subset_closure (mem_range_self y)),?_⟩
    rw [e]
    exact Or.inl (subset_closure (mem_range_self x))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.intersecting_compact_cores_on_puncture
