import TwoAxisHelicoid.ComplexPunctureTail
import TwoAxisHelicoid.ConnectedTailBoundedCover

namespace TwoAxisHelicoid
open Set Bornology

/-- An ordered proper local projection of a subend of a once-punctured
compact complex curve has one sheet. Compact control is measured in the
original punctured curve, which avoids treating the inner boundary of an
open subend as a new spatial end. -/
theorem punctured_curve_ordered_end_projection_injective
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M] [T2Space M]
    (p : M) {S : Set {q : M // q ≠ p}} (hSopen : IsOpen S) (hScompact : IsCompact Sᶜ)
    {B Z : Type*} [TopologicalSpace B] [PreconnectedSpace B] [Bornology Z]
    {f : S → B} {h : S → ℝ} {j : B → Z}
    (hp : IsProperMap f) (hh : Continuous h) (hl : IsLocalHomeomorph f)
    (hsep : ∀ d e, f d = f e → h d = h e → d = e)
    (hunbounded : ¬ IsBounded (range j))
    (hcontrol : ∀ K : Set {q : M // q ≠ p}, IsCompact K →
      IsBounded ((j ∘ f) '' (Subtype.val ⁻¹' K))) :
    Function.Injective f := by
  obtain ⟨U,_hUopen,hUconn,hUc,hUS⟩ := compact_complex_puncture_connected_tail p hScompact
  have hUSub : U ⊆ S := by
    intro q hq
    by_contra hn
    exact (Set.disjoint_left.mp hUS) hq hn
  have hconn : IsPreconnected (Subtype.val ⁻¹' U : Set S) :=
    hUconn.preimage_of_isOpenMap Subtype.val_injective hSopen.isOpenMap_subtype_val
      (fun q hq => ⟨⟨q,hUSub hq⟩,rfl⟩)
  apply ordered_proper_local_homeomorph_injective_of_bounded_complement hp hh hl hsep hconn hunbounded
  exact hcontrol Uᶜ hUc

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_curve_ordered_end_projection_injective
