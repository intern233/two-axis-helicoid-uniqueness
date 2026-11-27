import TwoAxisHelicoid.TorusPunctureFundamental
import TwoAxisHelicoid.LatticeSignDoubleCover

namespace TwoAxisHelicoid
open Complex Set Topology

theorem latticeSignCoverMk_translate (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (z : ℂ) (σ : ZMod 2) (ω₀ : L.lattice) :
    latticeSignCoverMk L χ (z+ω₀.1,σ) = latticeSignCoverMk L χ (z,σ-χ ω₀) := by
  apply (latticeSignCoverMk_eq L χ _ _).mpr
  exact ⟨ω₀,by simp,by simp⟩

theorem latticeSignCoverMk_fiber_injective (L : PeriodPair) (χ : L.lattice →+ ZMod 2) (z : ℂ) :
    Function.Injective (fun σ : ZMod 2 => latticeSignCoverMk L χ (z,σ)) := by
  intro σ τ he
  obtain ⟨ω₀,hω,hχ⟩ := (latticeSignCoverMk_eq L χ _ _).mp he
  have hω0 : ω₀ = 0 := by
    apply Subtype.ext
    change (ω₀ : ℂ) = 0
    simpa only [sub_self] using hω.symm
  rw [hω0,map_zero] at hχ
  exact sub_eq_zero.mp hχ

/-- Monodromy of the actual compact sign cover is computed by the
endpoint displacement of any continuous plane lift of the loop. -/
theorem latticeSignCover_monodromy_of_lift (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (z : ℂ) (γ : Path (periodTorusProjection L z) (periodTorusProjection L z))
    (f : C(unitInterval,ℂ)) (hf : periodTorusProjection L ∘ f = γ)
    (h0 : f 0 = z) (ω₀ : L.lattice) (h1 : f 1 = z+ω₀.1) (σ : ZMod 2) :
    ((latticeSignCoverProjection_isCoveringMap L χ).monodromy (.mk γ)
      ⟨latticeSignCoverMk L χ (z,σ),rfl⟩).1 = latticeSignCoverMk L χ (z,σ-χ ω₀) := by
  let g : C(unitInterval,LatticeSignCover L χ) :=
    ⟨fun s => latticeSignCoverMk L χ (f s,σ),
      QuotientAddGroup.continuous_mk.comp (f.continuous.prodMk continuous_const)⟩
  have hpg : latticeSignCoverProjection L χ ∘ g = γ := hf
  have hg0 : g 0 = latticeSignCoverMk L χ (z,σ) := by
    change latticeSignCoverMk L χ (f 0,σ) = _
    rw [h0]
  rw [(latticeSignCoverProjection_isCoveringMap L χ).monodromy_eq_apply_one hpg hg0]
  change latticeSignCoverMk L χ (f 1,σ) = _
  rw [h1,latticeSignCoverMk_translate]

theorem latticeSignCover_generator_monodromy (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (i : Fin 2) (σ : ZMod 2) :
    ((latticeSignCoverProjection_isCoveringMap L χ).monodromy (periodTorusGeneratorClass L i).asHom
      ⟨latticeSignCoverMk L χ (periodBasisLine L 0 0,σ),rfl⟩).1 =
      latticeSignCoverMk L χ (periodBasisLine L 0 0,σ-χ (periodGeneratorPeriod L i)) := by
  let f : C(unitInterval,ℂ) := ⟨fun s => periodBasisLine L i s,
    (continuous_subtype_val.comp (puncturedBasisLine_continuous L i)).comp continuous_subtype_val⟩
  have h0 : f 0 = periodBasisLine L 0 0 := by simp [f,periodBasisLine]
  have h1 : f 1 = periodBasisLine L 0 0+(periodGeneratorPeriod L i).1 := by
    simp [f,periodBasisLine,periodGeneratorPeriod_val]
  exact latticeSignCover_monodromy_of_lift L χ (periodBasisLine L 0 0)
    ((puncturedTorusGeneratorLoop L i).map continuous_subtype_val) f rfl h0
      (periodGeneratorPeriod L i) h1 σ

theorem latticeSignCover_generator_lift_closed_iff (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (i : Fin 2) (σ : ZMod 2) :
    ((latticeSignCoverProjection_isCoveringMap L χ).monodromy (periodTorusGeneratorClass L i).asHom
      ⟨latticeSignCoverMk L χ (periodBasisLine L 0 0,σ),rfl⟩).1 =
      latticeSignCoverMk L χ (periodBasisLine L 0 0,σ) ↔ χ (periodGeneratorPeriod L i) = 0 := by
  rw [latticeSignCover_generator_monodromy,(latticeSignCoverMk_fiber_injective L χ _).eq_iff]
  exact sub_eq_self

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.latticeSignCover_monodromy_of_lift
#print axioms TwoAxisHelicoid.latticeSignCover_generator_monodromy
