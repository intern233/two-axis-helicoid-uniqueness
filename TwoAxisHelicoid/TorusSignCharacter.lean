import TwoAxisHelicoid.LatticeSignMonodromy

namespace TwoAxisHelicoid
open Complex Set Topology

/-- The lattice sign character, transported by the fundamental group
isomorphism constructed from actual plane lifts. -/
noncomputable def torusSignCharacter (L : PeriodPair) (χ : L.lattice →+ ZMod 2) (z : ℂ) :
    FundamentalGroup (PeriodTorus L) (periodTorusProjection L z) →* Multiplicative (ZMod 2) :=
  χ.toMultiplicative.comp
    ((L.latticeEquivProd.symm.toAddEquiv.toMultiplicative).toMonoidHom.comp
      (periodTorusFundamentalGroupEquiv L z).toMonoidHom)

theorem torusSignCharacter_of_lift (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (z : ℂ) (γ : Path (periodTorusProjection L z) (periodTorusProjection L z))
    (f : C(unitInterval,ℂ)) (hf : periodTorusProjection L ∘ f = γ)
    (h0 : f 0 = z) (ω₀ : L.lattice) (h1 : f 1 = z+ω₀.1) :
    torusSignCharacter L χ z (.of (.mk γ)) = Multiplicative.ofAdd (χ ω₀) := by
  change Multiplicative.ofAdd (χ (L.latticeEquivProd.symm
    ((periodTorusFundamentalGroupEquiv L z (.of (.mk γ))).toAdd))) = _
  rw [periodTorusFundamentalGroupEquiv_of_lift L z γ f hf h0 ω₀ h1]
  simp

/-- Every actual loop in the compact torus has a plane lift whose
endpoint displacement is a lattice vector. -/
theorem periodTorus_loop_plane_lift (L : PeriodPair) (z : ℂ)
    (γ : Path (periodTorusProjection L z) (periodTorusProjection L z)) :
    ∃ f : C(unitInterval,ℂ), ∃ ω₀ : L.lattice,
      periodTorusProjection L ∘ f = γ ∧ f 0 = z ∧ f 1 = z+ω₀.1 := by
  let cov := (periodTorusProjection_isAddQuotientCoveringMap L).isCoveringMap
  let f := cov.liftPath γ z γ.source
  have hf : periodTorusProjection L ∘ f = γ := cov.liftPath_lifts γ z γ.source
  have h0 : f 0 = z := cov.liftPath_zero γ z γ.source
  have h1 : periodTorusProjection L (f 1) = periodTorusProjection L z :=
    (congrFun hf 1).trans γ.target
  have hm : f 1-z ∈ L.lattice := QuotientAddGroup.eq_iff_sub_mem.mp h1
  refine ⟨f,⟨f 1-z,hm⟩,hf,h0,?_⟩
  dsimp only
  ring

/-- The character computes the monodromy of the actual double cover
on every loop, rather than only on two selected representatives. -/
theorem latticeSignCover_loop_monodromy (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (z : ℂ) (γ : Path (periodTorusProjection L z) (periodTorusProjection L z)) (σ : ZMod 2) :
    ((latticeSignCoverProjection_isCoveringMap L χ).monodromy (.mk γ)
      ⟨latticeSignCoverMk L χ (z,σ),rfl⟩).1 =
      latticeSignCoverMk L χ (z,σ-(torusSignCharacter L χ z (.of (.mk γ))).toAdd) := by
  obtain ⟨f,ω₀,hf,h0,h1⟩ := periodTorus_loop_plane_lift L z γ
  rw [torusSignCharacter_of_lift L χ z γ f hf h0 ω₀ h1]
  exact latticeSignCover_monodromy_of_lift L χ z γ f hf h0 ω₀ h1 σ

theorem latticeSignCover_loop_closed_iff (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (z : ℂ) (γ : Path (periodTorusProjection L z) (periodTorusProjection L z)) (σ : ZMod 2) :
    ((latticeSignCoverProjection_isCoveringMap L χ).monodromy (.mk γ)
      ⟨latticeSignCoverMk L χ (z,σ),rfl⟩).1 = latticeSignCoverMk L χ (z,σ) ↔
      torusSignCharacter L χ z (.of (.mk γ)) = 1 := by
  rw [latticeSignCover_loop_monodromy,(latticeSignCoverMk_fiber_injective L χ z).eq_iff,
    sub_eq_self]
  rfl

theorem torusSignCharacter_generator (L : PeriodPair) (χ : L.lattice →+ ZMod 2) (i : Fin 2) :
    torusSignCharacter L χ (periodBasisLine L 0 0) (periodTorusGeneratorClass L i) =
      Multiplicative.ofAdd (χ (periodGeneratorPeriod L i)) := by
  change Multiplicative.ofAdd (χ (L.latticeEquivProd.symm
    ((periodTorusBasedFundamentalGroupEquiv L (periodTorusGeneratorClass L i)).toAdd))) = _
  rw [periodTorusGeneratorClass_coordinates]
  rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodTorus_loop_plane_lift
#print axioms TwoAxisHelicoid.latticeSignCover_loop_monodromy
