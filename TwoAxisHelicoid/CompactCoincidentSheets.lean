import TwoAxisHelicoid.CertifiedCompactDoublePoints
import Mathlib.Topology.Connected.Clopen

namespace TwoAxisHelicoid
open Set Filter Topology

/-- On a connected noncompact surface, compactly confined double points
cannot all be coincident sheet germs. Their projection would be both
open, by coincidence of the two local images, and compact. -/
theorem injective_of_compact_coincident_sheet_germs {M E : Type*}
    [TopologicalSpace M] [T2Space M] [PreconnectedSpace M] [NoncompactSpace M]
    [TopologicalSpace E] [T2Space E] (F : M → E) (hF : Continuous F)
    (loc : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn F U)
    {K : Set (M × M)} (hK : IsCompact K) (bound : immersionDoublePoints F ⊆ K)
    (coincide : ∀ x y : M, x ≠ y → F x = F y → ∀ V ∈ 𝓝 y, ∀ᶠ p in 𝓝 x, F p ∈ F '' V) :
    Function.Injective F := by
  let S := Prod.fst '' immersionDoublePoints F
  have compact : IsCompact S := (hK.of_isClosed_subset (isClosed_immersionDoublePoints hF loc) bound).image continuous_fst
  have op : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x ⟨⟨u,v⟩,h,rfl⟩
    obtain ⟨U,V,hU,hV,hu,hv,dis⟩ := t2_separation h.2
    filter_upwards [hU.mem_nhds hu,coincide u v h.2 h.1 V (hV.mem_nhds hv)] with p hp hnear
    obtain ⟨q,hq,heq⟩ := hnear
    exact ⟨(p,q),⟨heq.symm,fun (eq : p=q) => Set.disjoint_left.mp dis hp (eq ▸ hq)⟩,rfl⟩
  have empty : S=∅ := (isClopen_iff.mp ⟨compact.isClosed,op⟩).resolve_right (fun all =>
    noncompact_univ M (all ▸ compact))
  intro x y same
  by_contra h
  have mem : x ∈ S := ⟨(x,y),⟨same,h⟩,rfl⟩
  rw [empty] at mem
  exact mem

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.injective_of_compact_coincident_sheet_germs
