import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff

namespace TwoAxisHelicoid
open Set Topology

/-- Any compact core of a punctured compact Hausdorff space has an open
neighborhood in the original compactification contained in a larger
compact punctured core. -/
theorem punctured_compact_core_neighborhood
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] {p : M}
    {C : Set {q : M // q ≠ p}} (hC : IsCompact C) :
    ∃ (K : Set {q : M // q ≠ p}) (U : Set M), IsCompact K ∧ IsOpen U ∧
      p ∉ U ∧ Subtype.val '' C ⊆ U ∧ U ⊆ Subtype.val '' K := by
  have hCi : IsCompact (Subtype.val '' C) := hC.image continuous_subtype_val
  have hCp : Subtype.val '' C ⊆ ({p}ᶜ : Set M) := by
    rintro x ⟨q,_,rfl⟩
    exact q.2
  obtain ⟨K₀,hK₀,hCK₀,hKp⟩ := exists_compact_between hCi isOpen_compl_singleton hCp
  let K : Set {q : M // q ≠ p} := Subtype.val ⁻¹' K₀
  have he : Subtype.val '' K = K₀ := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact hq
    · intro hx
      exact ⟨⟨x,hKp hx⟩,hx,rfl⟩
  have hK : IsCompact K := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rwa [he]
  refine ⟨K,interior K₀,hK,isOpen_interior,?_,hCK₀,?_⟩
  · intro hp
    exact hKp (interior_subset hp) rfl
  · rw [he]
    exact interior_subset

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_compact_core_neighborhood
