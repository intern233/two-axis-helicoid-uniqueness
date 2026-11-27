module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Connected.PathConnected

public section
namespace TwoAxisHelicoid
open Set Topology

/-- A compact subset of a locally compact, path-connected space with a
countable compact exhaustion lies in one relatively compact connected
open neighborhood. The neighborhood can also contain a prescribed point. -/
theorem compact_in_connected_open_neighborhood {M : Type*} [TopologicalSpace M] [T2Space M]
    [LocallyCompactSpace M] [SigmaCompactSpace M] [LocallyConnectedSpace M] [PathConnectedSpace M]
    (p : M) {K : Set M} (compact : IsCompact K) :
    ∃ V : Set M, IsOpen V ∧ IsConnected V ∧ IsCompact (closure V) ∧ p∈V ∧ K⊆V := by
  let E := CompactExhaustion.choice M
  let V (n : ℕ) := connectedComponentIn (interior (E n)) p
  have inc : Monotone V := fun _ _ nm => connectedComponentIn_mono p (interior_mono (E.subset nm))
  have opened (n : ℕ) : IsOpen (V n) := isOpen_interior.connectedComponentIn
  have cover (x : M) : x∈⋃ n, V n := by
    let γ := (PathConnectedSpace.joined p x).somePath
    obtain ⟨n,sub⟩ := E.exists_superset_of_isCompact (isCompact_range γ.continuous)
    have c : IsPreconnected (range γ) := isPreconnected_range γ.continuous
    refine mem_iUnion.mpr ⟨n+1,?_⟩
    exact c.subset_connectedComponentIn ⟨0,γ.source⟩ (sub.trans (E.subset_interior_succ _)) ⟨1,γ.target⟩
  obtain ⟨n,inside⟩ := (compact.insert p).elim_directed_cover V opened (fun x _ => cover x) inc.directed_le
  have base := inside (mem_insert p K)
  have bound : closure (V n)⊆E n := closure_minimal
    ((connectedComponentIn_subset (interior (E n)) p).trans interior_subset) (E.isCompact n).isClosed
  exact ⟨V n,opened n,⟨⟨p,base⟩,isPreconnected_connectedComponentIn⟩,
    (E.isCompact n).of_isClosed_subset isClosed_closure bound,base,(subset_insert p K).trans inside⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_in_connected_open_neighborhood
