import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace TwoAxisHelicoid
open Set Topology

/-- A homeomorphism of two nonempty open subsets, as a chart on their
ambient spaces, with its values on the source recorded. -/
theorem open_coordinate_of_subsets {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {S : Set M} {T : Set N} (hs : IsOpen S) (ht : IsOpen T) (nonempty : Nonempty S) (E : S ≃ₜ T) :
    ∃ d : OpenPartialHomeomorph M N, d.source=S ∧ d.target=T ∧ ∀ x : S, d x=(E x).1 := by
  let := nonempty
  let : Nonempty T := nonempty.map E
  let i := hs.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : S → M)
  let j := ht.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : T → N)
  let d := i.symm.trans (E.toOpenPartialHomeomorph.trans j)
  have it : i.target=S := by simp [i,IsOpenEmbedding.toOpenPartialHomeomorph_target]
  have jt : j.target=T := by simp [j,IsOpenEmbedding.toOpenPartialHomeomorph_target]
  have isrc : i.source=univ := rfl
  have jsrc : j.source=univ := rfl
  refine ⟨d,?_,?_,?_⟩
  · ext x
    change (x∈i.target ∧ i.symm x∈E.toOpenPartialHomeomorph.source ∧ E (i.symm x)∈j.source) ↔ x∈S
    simp [it,jsrc]
  · ext y
    change (y∈j.target ∧ j.symm y∈E.toOpenPartialHomeomorph.target) ∧ E.symm (j.symm y)∈i.source ↔ y∈T
    simp [jt,isrc]
  · intro x
    change (E (i.symm x.1)).1=(E x).1
    rw [show i.symm x.1=x from hs.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.open_coordinate_of_subsets
