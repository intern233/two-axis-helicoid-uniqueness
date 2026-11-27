import TwoAxisHelicoid.TorusSignCharacter

namespace TwoAxisHelicoid
open Set Topology

theorem periodGeneratorPeriod_generate_lattice (L : PeriodPair) (ω₀ : L.lattice) :
    ω₀ = (L.latticeEquivProd ω₀).1 • periodGeneratorPeriod L 0+
      (L.latticeEquivProd ω₀).2 • periodGeneratorPeriod L 1 := by
  apply L.latticeEquivProd.injective
  simp [periodGeneratorPeriod]

theorem latticeCharacter_eq_zero_of_generators (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (h0 : χ (periodGeneratorPeriod L 0) = 0) (h1 : χ (periodGeneratorPeriod L 1) = 0) : χ = 0 := by
  ext ω₀
  rw [periodGeneratorPeriod_generate_lattice L ω₀,map_add,map_zsmul,map_zsmul,h0,h1]
  simp

theorem latticeSignCover_fiber_representative (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (z : ℂ) (q : LatticeSignCover L χ) (hq : latticeSignCoverProjection L χ q = periodTorusProjection L z) :
    ∃ σ : ZMod 2, latticeSignCoverMk L χ (z,σ) = q := by
  have he : latticeSignCoverProjection L χ q =
      latticeSignCoverProjection L χ (latticeSignCoverMk L χ (z,0)) := hq
  rcases (latticeSignCoverProjection_fibers L χ q _).mp he with he | he
  · exact ⟨0,he.symm⟩
  · rw [latticeSignCoverDeck_mk,zero_add] at he
    exact ⟨1,he.symm⟩

/-- A global section forces the actual lift of each generating loop to
close, so it annihilates both lattice generators. -/
theorem latticeSignCover_section_character_zero (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (s : C(PeriodTorus L,LatticeSignCover L χ))
    (hs : ∀ q, latticeSignCoverProjection L χ (s q) = q) : χ = 0 := by
  have hgen (i : Fin 2) : χ (periodGeneratorPeriod L i) = 0 := by
    let z₀ := periodBasisLine L 0 0
    let b := (puncturedTorusCenter L).1
    obtain ⟨σ,hσ⟩ := latticeSignCover_fiber_representative L χ z₀ (s b) (hs b)
    let γ : Path b b := (puncturedTorusGeneratorLoop L i).map continuous_subtype_val
    let β : C(unitInterval,LatticeSignCover L χ) := ⟨s ∘ γ,s.continuous.comp γ.continuous⟩
    have hβ : latticeSignCoverProjection L χ ∘ β = γ := funext fun u => hs (γ u)
    have hβ0 : β 0 = latticeSignCoverMk L χ (z₀,σ) := by
      change s (γ 0) = _
      rw [γ.source]
      exact hσ.symm
    have hβ1 : β 1 = latticeSignCoverMk L χ (z₀,σ) := by
      change s (γ 1) = _
      rw [γ.target]
      exact hσ.symm
    apply (latticeSignCover_generator_lift_closed_iff L χ i σ).mp
    exact ((latticeSignCoverProjection_isCoveringMap L χ).monodromy_eq_apply_one hβ hβ0).trans hβ1
  exact latticeCharacter_eq_zero_of_generators L χ (hgen 0) (hgen 1)

theorem latticeSignCover_zero_character_has_section (L : PeriodPair) :
    ∃ s : C(PeriodTorus L,LatticeSignCover L 0),
      ∀ q, latticeSignCoverProjection L 0 (s q) = q := by
  let f : ℂ → LatticeSignCover L 0 := fun z => latticeSignCoverMk L 0 (z,0)
  have hp (z ω₀ : ℂ) (hω : ω₀ ∈ L.lattice) : f (z+ω₀) = f z := by
    apply (latticeSignCoverMk_eq L 0 _ _).mpr
    exact ⟨⟨ω₀,hω⟩,by simp,by simp⟩
  let s := periodTorusLift L f hp
  have hc : Continuous s := by
    apply (QuotientAddGroup.isQuotientMap_mk L.lattice.toAddSubgroup).continuous_iff.mpr
    exact QuotientAddGroup.continuous_mk.comp (continuous_id.prodMk continuous_const)
  refine ⟨⟨s,hc⟩,?_⟩
  intro q
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  rfl

/-- Topological triviality is proved for the actual quotient cover,
independently of the holomorphic-section calculation. -/
theorem latticeSignCover_has_section_iff (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    (∃ s : C(PeriodTorus L,LatticeSignCover L χ),
      ∀ q, latticeSignCoverProjection L χ (s q) = q) ↔ χ = 0 := by
  constructor
  · rintro ⟨s,hs⟩
    exact latticeSignCover_section_character_zero L χ s hs
  · rintro rfl
    exact latticeSignCover_zero_character_has_section L

theorem latticeSpinParity_zero_iff_even (L : PeriodPair) (m : ℤ) :
    latticeSpinParity L m = 0 ↔ Even m := by
  constructor
  · intro he
    have hm : (m : ZMod 2) = 0 := by
      have h := congrArg (fun χ : L.lattice →+ ZMod 2 => χ (periodGeneratorPeriod L 1)) he
      simpa [latticeSpinParity_generator] using h
    exact ZMod.intCast_eq_zero_iff_even.mp hm
  · intro hm
    have hm0 : (m : ZMod 2) = 0 := ZMod.intCast_eq_zero_iff_even.mpr hm
    ext ω₀
    change ((m*(L.latticeEquivProd ω₀).2 : ℤ) : ZMod 2) = 0
    push_cast
    rw [hm0,zero_mul]

theorem integerSignCover_has_section_iff_even (L : PeriodPair) (m : ℤ) :
    (∃ s : C(PeriodTorus L,LatticeSignCover L (latticeSpinParity L m)),
      ∀ q, latticeSignCoverProjection L (latticeSpinParity L m) (s q) = q) ↔ Even m := by
  rw [latticeSignCover_has_section_iff,latticeSpinParity_zero_iff_even]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.latticeSignCover_has_section_iff
#print axioms TwoAxisHelicoid.integerSignCover_has_section_iff_even
