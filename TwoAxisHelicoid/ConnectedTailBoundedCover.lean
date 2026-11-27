import TwoAxisHelicoid.ConnectedTailCover
import Mathlib.Topology.Bornology.Basic

namespace TwoAxisHelicoid
open Set Bornology

/-- A bounded image of the omitted portion leaves an entire far fiber in
the chosen subend. Boundedness is measured in the ambient base coordinates,
so no improper compactness claim about an open annulus is needed. -/
theorem exists_full_fiber_of_bounded_complement_image {E B Z : Type*} [Bornology Z]
    {f : E → B} {j : B → Z} {U : Set E}
    (hunbounded : ¬ IsBounded (range j)) (hbounded : IsBounded ((j ∘ f) '' Uᶜ)) :
    ∃ b : B, f ⁻¹' {b} ⊆ U := by
  by_contra hn
  push Not at hn
  apply hunbounded
  apply hbounded.subset
  rintro z ⟨b,rfl⟩
  obtain ⟨e,he,hnot⟩ := Set.not_subset.mp (hn b)
  exact ⟨e,hnot,congrArg j he⟩

theorem ordered_proper_local_homeomorph_injective_of_bounded_complement {E B Z : Type*}
    [TopologicalSpace E] [TopologicalSpace B] [PreconnectedSpace B] [Bornology Z]
    {f : E → B} {h : E → ℝ} {j : B → Z}
    (hp : IsProperMap f) (hh : Continuous h) (hl : IsLocalHomeomorph f)
    (hsep : ∀ d e, f d = f e → h d = h e → d = e)
    {U : Set E} (hU : IsPreconnected U)
    (hunbounded : ¬ IsBounded (range j)) (hbounded : IsBounded ((j ∘ f) '' Uᶜ)) :
    Function.Injective f := by
  obtain ⟨b,hb⟩ := exists_full_fiber_of_bounded_complement_image hunbounded hbounded
  exact ordered_proper_local_homeomorph_injective_of_connected_full_fiber hp hh hl hsep hU b hb

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ordered_proper_local_homeomorph_injective_of_bounded_complement
