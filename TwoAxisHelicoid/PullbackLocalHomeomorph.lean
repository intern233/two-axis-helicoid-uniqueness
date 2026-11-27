import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Constructions.SumProd

namespace TwoAxisHelicoid
open Set Topology

abbrev CoverPullback {A B E : Type*} (f : A → B) (g : E → B) :=
  {v : A × E // f v.1 = g v.2}

def coverPullbackProjection {A B E : Type*} (f : A → B) (g : E → B) :
    CoverPullback f g → A := fun q => q.1.1

theorem coverPullbackProjection_continuous {A B E : Type*}
    [TopologicalSpace A] [TopologicalSpace E] (f : A → B) (g : E → B) :
    Continuous (coverPullbackProjection f g) := continuous_subtype_val.fst

/-- Base change of an open map is open in the actual pullback topology. -/
theorem coverPullbackProjection_isOpenMap {A B E : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E]
    {f : A → B} {g : E → B} (hf : Continuous f) (hg : IsOpenMap g) :
    IsOpenMap (coverPullbackProjection f g) := by
  intro W hW
  obtain ⟨O,hO,rfl⟩ := isOpen_induced_iff.mp hW
  apply isOpen_iff_mem_nhds.mpr
  rintro a ⟨q,hq,rfl⟩
  obtain ⟨U,V,hU,hqU,hV,hqV,hUV⟩ := mem_nhds_prod_iff'.mp (hO.mem_nhds hq)
  apply Filter.mem_of_superset
    ((hU.inter ((hg V hV).preimage hf)).mem_nhds
      (show q.1.1 ∈ U ∩ f ⁻¹' (g '' V) from ⟨hqU,q.1.2,hqV,q.2.symm⟩))
  rintro a ⟨haU,e,heV,hea⟩
  exact ⟨⟨(a,e),hea.symm⟩,hUV ⟨haU,heV⟩,rfl⟩

/-- A local homeomorphism remains a local homeomorphism after pullback. -/
theorem coverPullbackProjection_isLocalHomeomorph {A B E : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E]
    {f : A → B} {g : E → B} (hf : Continuous f) (hg : IsLocalHomeomorph g) :
    IsLocalHomeomorph (coverPullbackProjection f g) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro q
  obtain ⟨e,hqe,he⟩ := hg q.1.2
  let S : Set (CoverPullback f g) := {r | r.1.2 ∈ e.source}
  have hS : IsOpen S := e.open_source.preimage continuous_subtype_val.snd
  refine ⟨S,hS.mem_nhds hqe,?_⟩
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (coverPullbackProjection_continuous f g).comp continuous_subtype_val
  · intro r s hrs
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext hrs
    apply e.injOn r.2 s.2
    rw [← he,← r.1.2,← s.1.2]
    exact congrArg f hrs
  · exact (coverPullbackProjection_isOpenMap hf hg.isOpenMap).comp hS.isOpenMap_subtype_val

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coverPullbackProjection_isLocalHomeomorph

