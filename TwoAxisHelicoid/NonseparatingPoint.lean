import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn

namespace TwoAxisHelicoid
open Set Topology

/-- A compact locally connected Hausdorff continuum has a nonseparating
point distinct from any specified base point, provided there is a second
point. The proof takes a minimal closed branch away from the base point. -/
theorem exists_nonseparating_point {M : Type*} [TopologicalSpace M] [T1Space M]
    [CompactSpace M] [ConnectedSpace M] [LocallyConnectedSpace M] (p b : M) (bp : b≠p) :
    ∃ x : M, x≠p ∧ IsConnected ({x}ᶜ : Set M) := by
  classical
  let C := fun x : M => connectedComponentIn ({x}ᶜ : Set M) p
  let D := fun x : M => (C x)ᶜ
  have openC (x : M) : IsOpen (C x) := isOpen_ne.connectedComponentIn
  have base {x : M} (h : x≠p) : p∈C x := mem_connectedComponentIn h.symm
  have tip (x : M) : x∈D x := fun h => connectedComponentIn_subset ({x}ᶜ : Set M) p h rfl
  have closureC {x : M} (h : x≠p) : closure (C x)=insert x (C x) := by
    have upper : closure (C x)⊆insert x (C x) := by
      intro z hz
      by_cases eq : z=x
      · exact Or.inl eq
      · let A := connectedComponentIn ({x}ᶜ : Set M) z
        have az : z∈A := mem_connectedComponentIn eq
        obtain ⟨w,wa,wc⟩ := mem_closure_iff.mp hz A isOpen_ne.connectedComponentIn az
        have same := (connectedComponentIn_eq wc).trans (connectedComponentIn_eq wa).symm
        exact Or.inr (show z∈C x from (show C x=A from same).symm ▸ az)
    have atTip : x∈closure (C x) := by
      by_contra miss
      have closed : IsClosed (C x) := closure_eq_iff_isClosed.mp (subset_antisymm (by
        intro z hz
        rcases upper hz with eq|hit
        · subst z; exact (miss hz).elim
        · exact hit) subset_closure)
      have whole := IsClopen.eq_univ ⟨closed,openC x⟩ ⟨p,base h⟩
      exact tip x (whole.symm ▸ mem_univ x)
    exact upper.antisymm (insert_subset atTip subset_closure)
  have nested {x y : M} (h : x≠p) (hy : y∈D x) (ne : y≠x) : D y⊆D x ∧ x∉D y := by
    have avoid : closure (C x)⊆({y}ᶜ : Set M) := by
      intro z hz eq
      change z=y at eq
      subst z
      exact ((closureC h ▸ hz) : y∈insert x (C x)).elim ne hy
    have sub : closure (C x)⊆C y := isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (base h)) avoid
    exact ⟨compl_subset_compl.mpr (subset_closure.trans sub),fun hx => hx (sub ((closureC h).symm ▸ mem_insert x (C x)))⟩
  let F := D '' ({p}ᶜ : Set M)
  have decrease {x y : M} (hx : x≠p) (hy : y∈D x) : D y⊆D x := by
    by_cases e : y=x
    · exact e ▸ Subset.rfl
    · exact (nested hx hy e).1
  obtain ⟨K,_,minimum⟩ := zorn_superset_nonempty F (fun chain belongs comparable non => by
    have directed : DirectedOn (· ⊇ ·) chain := by
      intro U u V v
      rcases comparable.total u v with h|h
      · exact ⟨U,u,Subset.rfl,h⟩
      · exact ⟨V,v,h,Subset.rfl⟩
    have closed (U : Set M) (u : U∈chain) : IsClosed U := by
      obtain ⟨x,_,rfl⟩ := belongs u
      exact (openC x).isClosed_compl
    have live (U : Set M) (u : U∈chain) : U.Nonempty := by
      obtain ⟨x,_,rfl⟩ := belongs u
      exact ⟨x,tip x⟩
    let _ : Nonempty chain := non.to_subtype
    obtain ⟨z,all⟩ := IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed directed live
      (fun U u => (closed U u).isCompact) closed
    obtain ⟨U,u⟩ := non
    obtain ⟨x,hx,eq⟩ := belongs u
    have zu : z∈D x := eq.symm ▸ mem_sInter.mp all U u
    have zp : z≠p := fun eq => zu (eq ▸ base hx)
    refine ⟨D z,⟨z,zp,rfl⟩,?_⟩
    intro U u
    obtain ⟨y,ny,eq⟩ := belongs u
    exact eq ▸ decrease ny (eq.symm ▸ mem_sInter.mp all U u)) (D b) ⟨b,bp,rfl⟩
  obtain ⟨x,hx,eq⟩ := minimum.prop
  have rest : D x⊆{x} := by
    intro z hz
    by_contra h
    have non : z≠p := fun e => hz (e ▸ base hx)
    obtain ⟨sub,missing⟩ := nested hx hz h
    have incl := minimum.le_of_le (show D z∈F from ⟨z,non,rfl⟩) (eq ▸ sub)
    exact missing (incl (eq ▸ tip x))
  have complement : C x=({x}ᶜ : Set M) := (connectedComponentIn_subset _ _).antisymm
    (fun z nz => by by_contra outside; exact nz (rest outside))
  exact ⟨x,hx,complement ▸ (show IsConnected (C x) from ⟨⟨p,base hx⟩,isPreconnected_connectedComponentIn⟩)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exists_nonseparating_point
