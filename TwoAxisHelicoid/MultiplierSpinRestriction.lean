import TwoAxisHelicoid.CompactMultiplierSpinBundle
import TwoAxisHelicoid.ImmersionSpatialSpin

namespace TwoAxisHelicoid
open Set Topology

variable (L : PeriodPair) (χ : L.lattice →+ ZMod 2)

/-- The compact unit spin bundle restricted over the punctured torus. -/
abbrev RestrictedCompactMultiplierSpin :=
  {s : CompactMultiplierSpinBundle L χ // (compactMultiplierSpinProjection L χ s).1 ≠ 0}

noncomputable def restrictedCompactSpinMk (x : PuncturedSignCover L χ × Circle) :
    RestrictedCompactMultiplierSpin L χ :=
  ⟨Quotient.mk _ (x.1.1,x.2),x.1.2⟩

theorem restrictedCompactSpinMk_isOpenQuotientMap :
    IsOpenQuotientMap (restrictedCompactSpinMk L χ) := by
  let q := Quotient.mk (spinPhaseSetoid (latticeSignCoverDeck L χ)
    (latticeSignCoverDeck_involutive L χ))
  let i : PuncturedSignCover L χ × Circle → LatticeSignCover L χ × Circle :=
    Prod.map Subtype.val id
  have hq := spinPhaseMk_isOpenQuotientMap (latticeSignCoverDeck L χ)
    (latticeSignCoverDeck_involutive L χ)
  have hi : IsOpenMap i :=
    (puncturedSignCover_open L χ).isOpenEmbedding_subtypeVal.isOpenMap.prodMap IsOpenMap.id
  refine ⟨?_,?_,?_⟩
  · rintro ⟨s,hs⟩
    obtain ⟨⟨e,u⟩,rfl⟩ := Quotient.exists_rep s
    exact ⟨(⟨e,hs⟩,u),rfl⟩
  · exact ((hq.continuous.comp (continuous_subtype_val.prodMap continuous_id)).subtype_mk _)
  · exact (hq.isOpenMap.comp hi).subtype_mk _

/-- Removing the fiber over the puncture commutes with the diagonal sign
quotient, including its topology. -/
noncomputable def multiplierSpinRestrictionHomeomorph :
    PuncturedMultiplierSpinBundle L χ ≃ₜ RestrictedCompactMultiplierSpin L χ := by
  let F : C(PuncturedSignCover L χ × Circle,RestrictedCompactMultiplierSpin L χ) :=
    ⟨_,(restrictedCompactSpinMk_isOpenQuotientMap L χ).continuous⟩
  have hF : IsQuotientMap F := (restrictedCompactSpinMk_isOpenQuotientMap L χ).isQuotientMap
  refine (Homeomorph.Quotient.congrRight (r' := Setoid.ker F) ?_).trans hF.homeomorph
  rintro ⟨e,u⟩ ⟨d,v⟩
  change ((e,u) = (d,v) ∨ (e,u) = (puncturedSignCoverDeck L χ d,-v)) ↔
    restrictedCompactSpinMk L χ (e,u) = restrictedCompactSpinMk L χ (d,v)
  rw [Subtype.ext_iff]
  change _ ↔ Quotient.mk _ (e.1,u) = Quotient.mk _ (d.1,v)
  rw [Quotient.eq]
  change _ ↔ (e.1,u) = (d.1,v) ∨ (e.1,u) = (latticeSignCoverDeck L χ d.1,-v)
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg (Prod.map Subtype.val id) h)
    · exact Or.inr (congrArg (Prod.map Subtype.val id) h)
  · rintro (h | h)
    · exact Or.inl (Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun w : LatticeSignCover L χ × Circle => w.2) h))
    · exact Or.inr (Prod.ext (Subtype.ext (congrArg Prod.fst h)) (congrArg (fun w : LatticeSignCover L χ × Circle => w.2) h))

theorem multiplierSpinRestrictionHomeomorph_mk (x : PuncturedSignCover L χ) (u : Circle) :
    multiplierSpinRestrictionHomeomorph L χ (Quotient.mk _ (x,u)) =
      restrictedCompactSpinMk L χ (x,u) := rfl

theorem multiplierSpinRestrictionHomeomorph_phase (u : Circle) (s : PuncturedMultiplierSpinBundle L χ) :
    (multiplierSpinRestrictionHomeomorph L χ
      (associatedSpinPhase _ (puncturedSignCoverDeck_involutive L χ) u s)).1 =
    associatedSpinPhase _ (latticeSignCoverDeck_involutive L χ) u
      (multiplierSpinRestrictionHomeomorph L χ s).1 := by
  obtain ⟨w,rfl⟩ := Quotient.exists_rep s
  rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.multiplierSpinRestrictionHomeomorph
#print axioms TwoAxisHelicoid.multiplierSpinRestrictionHomeomorph_phase
