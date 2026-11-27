module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Separation.Hausdorff

public section
namespace TwoAxisHelicoid
open Set Topology

/-- When a compact set is surrounded by a relatively compact open
neighborhood with connected nonempty frontier, the frontier belongs
to one connected tail with compact complement. -/
theorem connected_tail_of_enclosing_frontier {M : Type*} [TopologicalSpace M] [T2Space M]
    [PreconnectedSpace M] [LocallyConnectedSpace M] {K V : Set M}
    (compact : IsCompact K) (inside : K⊆V) (op : IsOpen V)
    (relatively : IsCompact (closure V)) (edge : IsConnected (frontier V)) :
    ∃ G : Set M, IsPreconnected G ∧ IsCompact Gᶜ ∧ Disjoint G K := by
  obtain ⟨p,hp⟩ := edge.nonempty
  have outside : frontier V⊆Kᶜ := fun x hx hk => hx.2 (op.interior_eq.symm ▸ inside hk)
  let G := connectedComponentIn Kᶜ p
  have pg : p∈G := mem_connectedComponentIn (outside hp)
  have go : IsOpen G := compact.isClosed.isOpen_compl.connectedComponentIn
  have sub : G⊆Kᶜ := connectedComponentIn_subset _ _
  have fg : frontier V⊆G := edge.isPreconnected.subset_connectedComponentIn hp outside
  have closed : IsClosed (V∪G) := by
    apply isClosed_of_closure_subset
    rw [closure_union]
    rintro x (hv|hg)
    · by_cases xv : x∈V
      · exact Or.inl xv
      · exact Or.inr (fg ⟨hv,fun h => xv (interior_subset h)⟩)
    · by_cases hk : x∈K
      · exact Or.inl (inside hk)
      · let W := connectedComponentIn Kᶜ x
        have wo : IsOpen W := compact.isClosed.isOpen_compl.connectedComponentIn
        have xw : x∈W := mem_connectedComponentIn hk
        obtain ⟨w,hw,wg⟩ := mem_closure_iff.mp hg W wo xw
        have eq : W=G := (connectedComponentIn_eq hw).trans (connectedComponentIn_eq wg).symm
        exact Or.inr (eq ▸ xw)
  have full := (isClopen_iff.mp (show IsClopen (V∪G) from ⟨closed,op.union go⟩)).resolve_left
    (show (V∪G).Nonempty from ⟨p,Or.inr pg⟩).ne_empty
  have bound : Gᶜ⊆closure V := fun x hx => subset_closure (((show x∈V∪G from full ▸ mem_univ x)).resolve_right hx)
  exact ⟨G,isPreconnected_connectedComponentIn,relatively.of_isClosed_subset go.isClosed_compl bound,
    disjoint_left.mpr fun x hx hk => sub hx hk⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.connected_tail_of_enclosing_frontier
