import TwoAxisHelicoid.LatticeSignCover

namespace TwoAxisHelicoid
open Set Topology
set_option maxHeartbeats 1000000

theorem latticeSignCoverProjection_deck (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (q : LatticeSignCover L χ) :
    latticeSignCoverProjection L χ (latticeSignCoverDeck L χ q) = latticeSignCoverProjection L χ q := by
  obtain ⟨v,rfl⟩ := Quotient.exists_rep q
  change latticeSignCoverProjection L χ
    (latticeSignCoverDeck L χ (latticeSignCoverMk L χ v)) = _
  rw [latticeSignCoverDeck_mk]
  rfl

theorem latticeSignCoverProjection_fibers (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (q r : LatticeSignCover L χ) :
    latticeSignCoverProjection L χ q = latticeSignCoverProjection L χ r ↔
      q = r ∨ q = latticeSignCoverDeck L χ r := by
  constructor
  · obtain ⟨v,rfl⟩ := Quotient.exists_rep q
    obtain ⟨w,rfl⟩ := Quotient.exists_rep r
    intro he
    change periodTorusProjection L v.1 = periodTorusProjection L w.1 at he
    have hm : v.1-w.1 ∈ L.lattice :=
      (QuotientAddGroup.eq_iff_sub_mem).mp he
    let ω : L.lattice := ⟨v.1-w.1,hm⟩
    rcases zmod_two_cases (v.2-w.2-χ ω) with hδ | hδ
    · left
      apply (latticeSignCoverMk_eq L χ v w).mpr
      exact ⟨ω,rfl,sub_eq_zero.mp hδ⟩
    · right
      change latticeSignCoverMk L χ v = latticeSignCoverDeck L χ (latticeSignCoverMk L χ w)
      rw [latticeSignCoverDeck_mk]
      apply (latticeSignCoverMk_eq L χ v (w.1,w.2+1)).mpr
      refine ⟨ω,rfl,?_⟩
      linear_combination hδ
  · rintro (rfl | rfl)
    · rfl
    · exact latticeSignCoverProjection_deck L χ r

/-- The prescribed sign character constructs an actual double cover of
the whole torus, with its quotient topology and two distinct local sheets. -/
theorem latticeSignCoverProjection_isCoveringMap (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    IsCoveringMap (latticeSignCoverProjection L χ) :=
  free_involution_quotient_isCoveringMap (latticeSignCoverDeck L χ)
    (latticeSignCoverDeck_involutive L χ) (latticeSignCoverDeck_ne L χ)
    (latticeSignCoverProjection_isQuotientMap L χ) (latticeSignCoverProjection_fibers L χ)

theorem latticeSignCoverProjection_two_sheets (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (b : PeriodTorus L) :
    ∃ q : LatticeSignCover L χ, latticeSignCoverProjection L χ q = b ∧
      latticeSignCoverProjection L χ (latticeSignCoverDeck L χ q) = b ∧
      latticeSignCoverDeck L χ q ≠ q ∧
      ∀ r, latticeSignCoverProjection L χ r = b → r = q ∨ r = latticeSignCoverDeck L χ q := by
  obtain ⟨q,hq⟩ := (latticeSignCoverProjection_isQuotientMap L χ).surjective b
  refine ⟨q,hq,(latticeSignCoverProjection_deck L χ q).trans hq,latticeSignCoverDeck_ne L χ q,?_⟩
  intro r hr
  exact (latticeSignCoverProjection_fibers L χ r q).mp (hr.trans hq.symm)

theorem latticeSignCoverMk_isLocalHomeomorph (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    IsLocalHomeomorph (latticeSignCoverMk L χ) :=
  ((latticeSignGraph L χ).isAddQuotientCoveringMap_of_comm
    (isDiscrete_iff_discreteTopology.mpr
      (inferInstanceAs (DiscreteTopology (latticeSignGraph L χ))))).isLocalHomeomorph

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.latticeSignCoverProjection_isCoveringMap
#print axioms TwoAxisHelicoid.latticeSignCoverProjection_two_sheets

