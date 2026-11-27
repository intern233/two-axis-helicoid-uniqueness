module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Homeomorph.Lemmas

public section
namespace TwoAxisHelicoid
open Set Topology

/-- Fill all components of the complement of a set except the component
containing the designated exterior point. -/
def fillAwayFrom {X : Type*} [TopologicalSpace X] (p : X) (U : Set X) : Set X :=
  (connectedComponentIn Uᶜ p)ᶜ

theorem subset_fillAwayFrom {X : Type*} [TopologicalSpace X] (p : X) (U : Set X) :
    U⊆fillAwayFrom p U := fun _ hx outside => (connectedComponentIn_subset _ _ outside) hx

theorem fillAwayFrom_mono {X : Type*} [TopologicalSpace X] (p : X) {U V : Set X}
    (inside : U⊆V) : fillAwayFrom p U⊆fillAwayFrom p V :=
  compl_subset_compl.mpr (connectedComponentIn_mono _ (compl_subset_compl.mpr inside))

theorem fillAwayFrom_eq_of_complement {X : Type*} [TopologicalSpace X] {p : X} {U : Set X}
    (outside : p∉U) (conn : IsPreconnected Uᶜ) : fillAwayFrom p U=U := by
  rw [fillAwayFrom,conn.connectedComponentIn outside,compl_compl]

theorem isOpen_fillAwayFrom {X : Type*} [TopologicalSpace X] {p : X} {U : Set X}
    (op : IsOpen U) : IsOpen (fillAwayFrom p U) := by
  unfold fillAwayFrom
  apply isOpen_compl_iff.mpr
  by_cases hp : p∈Uᶜ
  · apply isClosed_of_closure_subset
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hp))
      (closure_minimal (connectedComponentIn_subset Uᶜ p) op.isClosed_compl)
  · rw [connectedComponentIn_eq_empty hp]
    exact isClosed_empty

/-- Filling a connected open set preserves connectedness. It suffices
that the components of the open filled set are open. This version also
applies at infinity when only finite points carry known local charts. -/
theorem fillAwayFrom_isConnected {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {p : X} {U : Set X} (outside : p∉U) (op : IsOpen U) (conn : IsConnected U)
    (components : ∀ x∈fillAwayFrom p U, IsOpen (connectedComponentIn (fillAwayFrom p U) x)) :
    IsConnected (fillAwayFrom p U) := by
  let F := fillAwayFrom p U
  let C := connectedComponentIn Uᶜ p
  have pc : p∈C := mem_connectedComponentIn outside
  have sub : U⊆F := subset_fillAwayFrom p U
  obtain ⟨u,hu⟩ := conn.nonempty
  have all (x : X) (hx : x∈F) : x∈connectedComponentIn F u := by
    let G := connectedComponentIn F x
    have xg : x∈G := mem_connectedComponentIn hx
    have gc : IsPreconnected G := isPreconnected_connectedComponentIn
    have meet : (G∩U).Nonempty := by
      by_contra miss
      have gu : G⊆Uᶜ := fun z hz hu' => miss ⟨z,hz,hu'⟩
      have cg : closure G⊆Uᶜ := closure_minimal gu op.isClosed_compl
      have stay : closure G⊆F := by
        intro y hy yc
        have toC := gc.closure.subset_connectedComponentIn hy cg
        have eq : C=connectedComponentIn Uᶜ y := connectedComponentIn_eq yc
        apply hx
        change x∈C
        rw [eq]
        exact toC (subset_closure xg)
      have closed : IsClosed G := isClosed_of_closure_subset
        (gc.closure.subset_connectedComponentIn (subset_closure xg) stay)
      have full := (isClopen_iff.mp ⟨closed,components x hx⟩).resolve_left (nonempty_of_mem xg).ne_empty
      have pg : p∈G := by simpa only [full] using (mem_univ p : p∈(univ : Set X))
      exact (connectedComponentIn_subset F x pg) pc
    obtain ⟨y,yg,yu⟩ := meet
    have uy : y∈connectedComponentIn F u := conn.isPreconnected.subset_connectedComponentIn hu sub yu
    have same : G=connectedComponentIn F u := (connectedComponentIn_eq yg).trans (connectedComponentIn_eq uy).symm
    exact same ▸ xg
  have eq : F=connectedComponentIn F u := Subset.antisymm all (connectedComponentIn_subset _ _)
  exact ⟨⟨u,sub hu⟩,(congrArg IsPreconnected eq).mpr isPreconnected_connectedComponentIn⟩

theorem homeomorph_maps_fillAwayFrom {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (p : X) (U : Set X) (outside : p∉U) :
    e '' fillAwayFrom p U=fillAwayFrom (e p) (e '' U) := by
  unfold fillAwayFrom
  calc
    e '' (connectedComponentIn Uᶜ p)ᶜ = (e '' connectedComponentIn Uᶜ p)ᶜ :=
      e.toEquiv.image_compl _
    _ = (connectedComponentIn (e '' Uᶜ) (e p))ᶜ := congrArg compl (e.image_connectedComponentIn (show p∈Uᶜ from outside))
    _ = (connectedComponentIn (e '' U)ᶜ (e p))ᶜ := by rw [show e '' Uᶜ=(e '' U)ᶜ from e.toEquiv.image_compl U]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.isOpen_fillAwayFrom
#print axioms TwoAxisHelicoid.fillAwayFrom_isConnected
#print axioms TwoAxisHelicoid.homeomorph_maps_fillAwayFrom
