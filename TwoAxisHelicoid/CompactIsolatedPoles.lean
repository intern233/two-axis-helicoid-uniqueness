import Mathlib.Topology.Compactness.Compact

namespace TwoAxisHelicoid
open Set

/-- A set which has no accumulation point in a compact space is finite.
The neighborhoods may contain their center as the only exceptional point. -/
theorem finite_of_locally_isolated_poles {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {P : Set X}
    (h : ∀ p : X, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, x ∈ P → x = p) :
    P.Finite := by
  classical
  choose U hU hp hP using h
  have hcover : (univ : Set X) ⊆ ⋃ p : X, U p := by
    intro p _
    exact mem_iUnion.mpr ⟨p,hp p⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  apply s.finite_toSet.subset
  intro x hx
  obtain ⟨p,hpx⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨hpS,hxU⟩ := mem_iUnion.mp hpx
  exact (hP p x hxU hx).symm ▸ hpS

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.finite_of_locally_isolated_poles
