import TwoAxisHelicoid.TorusGeneratingCoreModels

namespace TwoAxisHelicoid
open Set Topology

/-- A genuine punctured-torus patch in a periodic surface carries a
generating core in a compact set of that very surface. The core,
its carrier and the compact set are all constructed from the patch. -/
theorem punctured_torus_patch_carries_compact_core {M : Type*} [TopologicalSpace M]
    (A : PeriodPair) (j : PuncturedPeriodTorus A → M) (hj : IsOpenEmbedding j) :
    ∃ (C : TorusGeneratingCoreModel A) (f : C.carrier → M) (K : Set M),
      IsOpenEmbedding f ∧ IsCompact K ∧ range f⊆K := by
  let _ := periodTorus_compactSpace A
  let _ : T1Space (PeriodTorus A) := QuotientAddGroup.t1Space_iff.mpr A.isClosed_lattice
  obtain ⟨C⟩ := exists_torus_generating_core_model A
  let S := {q : PuncturedPeriodTorus A | q.1∈closure C.carrier}
  have imageS : Subtype.val '' S=closure C.carrier := by
    ext q
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact hw
    · intro hq
      have off : q≠0 := fun eq => C.closure_avoids (eq ▸ hq)
      exact ⟨⟨q,off⟩,hq,rfl⟩
  have compact : IsCompact S := Subtype.isCompact_iff.mpr (imageS ▸ isClosed_closure.isCompact)
  let i (q : C.carrier) : PuncturedPeriodTorus A := ⟨q.1,fun eq => C.closure_avoids (eq ▸ subset_closure q.2)⟩
  have opp : IsOpen {q : PeriodTorus A | q≠0} := isClosed_singleton.isOpen_compl
  have openInclusion : IsOpenEmbedding i := (IsOpenEmbedding.of_comp_iff i opp.isOpenEmbedding_subtypeVal).mp
    C.isOpen_carrier.isOpenEmbedding_subtypeVal
  refine ⟨C,j ∘ i,j '' S,hj.comp openInclusion,compact.image hj.continuous,?_⟩
  rintro _ ⟨q,rfl⟩
  exact ⟨i q,subset_closure q.2,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_torus_patch_carries_compact_core
