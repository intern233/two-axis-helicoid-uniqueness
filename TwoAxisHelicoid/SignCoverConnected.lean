import TwoAxisHelicoid.SignCoverSections
import Mathlib.Topology.Connected.TotallyDisconnected

namespace TwoAxisHelicoid
open Set Topology

theorem latticeSignCharacter_surjective_of_ne_zero (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (hχ : χ ≠ 0) : Function.Surjective χ := by
  classical
  have hn : ∃ ω₀, χ ω₀ ≠ 0 := by
    by_contra he
    push Not at he
    exact hχ (AddMonoidHom.ext he)
  obtain ⟨ω₀,hω⟩ := hn
  have hω1 : χ ω₀ = 1 := (zmod_two_cases (χ ω₀)).resolve_left hω
  intro σ
  rcases zmod_two_cases σ with rfl | rfl
  · exact ⟨0,map_zero χ⟩
  · exact ⟨ω₀,hω1⟩

/-- For a nontrivial sign character the image of a single copy of the
plane already covers the entire quotient total space. -/
theorem latticeSignCover_pathConnected_of_nonzero (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) (hχ : χ ≠ 0) : PathConnectedSpace (LatticeSignCover L χ) := by
  have hs : Function.Surjective (fun z : ℂ => latticeSignCoverMk L χ (z,0)) := by
    intro q
    obtain ⟨v,rfl⟩ := Quotient.exists_rep q
    obtain ⟨ω₀,hω⟩ := latticeSignCharacter_surjective_of_ne_zero L χ hχ (-v.2)
    refine ⟨v.1+ω₀.1,?_⟩
    change latticeSignCoverMk L χ (v.1+ω₀.1,0) = latticeSignCoverMk L χ v
    rw [latticeSignCoverMk_translate,hω,zero_sub,neg_neg]
  exact hs.pathConnectedSpace
    (QuotientAddGroup.continuous_mk.comp (continuous_id.prodMk continuous_const))

theorem latticeSignCover_zero_not_preconnected (L : PeriodPair) :
    ¬ PreconnectedSpace (LatticeSignCover L 0) := by
  intro hcon
  let := hcon
  have hf (v w : ℂ × ZMod 2)
      (he : latticeSignCoverMk L 0 v = latticeSignCoverMk L 0 w) : v.2 = w.2 := by
    obtain ⟨ω₀,_,hχ⟩ := (latticeSignCoverMk_eq L 0 v w).mp he
    exact sub_eq_zero.mp hχ
  let f := quotientFiberDescend (latticeSignCoverMk L 0) Quotient.mk_surjective Prod.snd
  have hc : Continuous f := quotientFiberDescend_continuous
    (QuotientAddGroup.isQuotientMap_mk (latticeSignGraph L 0)) Prod.snd hf continuous_snd
  have hmk (v : ℂ × ZMod 2) : f (latticeSignCoverMk L 0 v) = v.2 :=
    quotientFiberDescend_apply _ _ Prod.snd hf v
  have he := TotallyDisconnectedSpace.eq_of_continuous f hc
    (latticeSignCoverMk L 0 (0,0)) (latticeSignCoverMk L 0 (0,1))
  rw [hmk,hmk] at he
  exact zero_ne_one he

theorem latticeSignCover_pathConnected_iff_nonzero (L : PeriodPair)
    (χ : L.lattice →+ ZMod 2) : PathConnectedSpace (LatticeSignCover L χ) ↔ χ ≠ 0 := by
  constructor
  · intro hcon he
    subst χ
    let := hcon
    exact latticeSignCover_zero_not_preconnected L inferInstance
  · exact latticeSignCover_pathConnected_of_nonzero L χ

theorem integerSignCover_pathConnected_iff_odd (L : PeriodPair) (m : ℤ) :
    PathConnectedSpace (LatticeSignCover L (latticeSpinParity L m)) ↔ Odd m := by
  rw [latticeSignCover_pathConnected_iff_nonzero,ne_eq,latticeSpinParity_zero_iff_even,
    Int.not_even_iff_odd]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.latticeSignCover_pathConnected_iff_nonzero
#print axioms TwoAxisHelicoid.integerSignCover_pathConnected_iff_odd
