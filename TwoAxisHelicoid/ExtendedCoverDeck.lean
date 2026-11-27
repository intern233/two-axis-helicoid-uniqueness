import TwoAxisHelicoid.SignCoverHomeomorphExtension

namespace TwoAxisHelicoid

/-- An isomorphism over the base between actual double covers
automatically preserves the nontrivial sheet interchange. -/
theorem signCoverHomeomorph_preserves_deck (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    {E : Type*} [TopologicalSpace E] {p : E → PeriodTorus L}
    (τ : E → E) (hf : ∀ x y, p x = p y ↔ x = y ∨ x = τ y)
    (H : LatticeSignCover L χ ≃ₜ E)
    (hH : ∀ q, p (H q) = latticeSignCoverProjection L χ q) (q : LatticeSignCover L χ) :
    H (latticeSignCoverDeck L χ q) = τ (H q) := by
  have he : p (H (latticeSignCoverDeck L χ q)) = p (H q) := by
    rw [hH,hH,latticeSignCoverProjection_deck]
  rcases (hf _ _).mp he with he | he
  · exact False.elim (latticeSignCoverDeck_ne L χ q (H.injective he))
  · exact he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.signCoverHomeomorph_preserves_deck
