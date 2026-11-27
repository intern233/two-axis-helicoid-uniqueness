import TwoAxisHelicoid.PeriodTorusTopology
import TwoAxisHelicoid.InvolutionDoubleCover
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Instances.ZMod

namespace TwoAxisHelicoid
open Set Topology
set_option maxHeartbeats 1000000

noncomputable def latticeSignGraphHom (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    L.lattice →+ ℂ × ZMod 2 where
  toFun ω := (ω.1,χ ω)
  map_zero' := by simp
  map_add' ω ν := by simp

noncomputable def latticeSignGraph (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    AddSubgroup (ℂ × ZMod 2) := (latticeSignGraphHom L χ).range

theorem latticeSignGraph_mem (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (v : ℂ × ZMod 2) : v ∈ latticeSignGraph L χ ↔
      ∃ ω : L.lattice, ω.1 = v.1 ∧ χ ω = v.2 := by
  change (∃ ω, (ω.1,χ ω) = v) ↔ _
  simp only [Prod.ext_iff]

theorem latticeSignGraph_fst_mem (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (v : latticeSignGraph L χ) : v.1.1 ∈ L.lattice := by
  obtain ⟨ω,hω,_⟩ := (latticeSignGraph_mem L χ v.1).mp v.2
  exact hω ▸ ω.2

noncomputable def latticeSignGraphBase (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    latticeSignGraph L χ → L.lattice := fun v => ⟨v.1.1,latticeSignGraph_fst_mem L χ v⟩

theorem latticeSignGraphBase_injective (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    Function.Injective (latticeSignGraphBase L χ) := by
  intro v w he
  obtain ⟨ω,hω,hχω⟩ := (latticeSignGraph_mem L χ v.1).mp v.2
  obtain ⟨ν,hν,hχν⟩ := (latticeSignGraph_mem L χ w.1).mp w.2
  have hfst : v.1.1 = w.1.1 := congrArg Subtype.val he
  have hων : ω = ν := Subtype.ext (hω.trans (hfst.trans hν.symm))
  apply Subtype.ext
  exact Prod.ext hfst (hχω.symm.trans ((congrArg χ hων).trans hχν))

instance latticeSignGraph_discrete (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    DiscreteTopology (latticeSignGraph L χ) :=
  DiscreteTopology.of_continuous_injective
    (continuous_subtype_val.fst.subtype_mk (latticeSignGraph_fst_mem L χ))
    (latticeSignGraphBase_injective L χ)

/-- The flat sign cover is defined over the whole compact torus. -/
abbrev LatticeSignCover (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :=
  (ℂ × ZMod 2) ⧸ latticeSignGraph L χ

noncomputable def latticeSignCoverMk (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    ℂ × ZMod 2 → LatticeSignCover L χ := QuotientAddGroup.mk

theorem latticeSignCoverMk_eq (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (v w : ℂ × ZMod 2) : latticeSignCoverMk L χ v = latticeSignCoverMk L χ w ↔
      ∃ ω : L.lattice, v.1-w.1 = ω.1 ∧ v.2-w.2 = χ ω := by
  rw [latticeSignCoverMk,QuotientAddGroup.eq_iff_sub_mem,latticeSignGraph_mem]
  simp only [Prod.fst_sub,Prod.snd_sub,eq_comm]

noncomputable def latticeSignCoverProjection (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    LatticeSignCover L χ → PeriodTorus L :=
  Quotient.lift (fun v => periodTorusProjection L v.1) (by
    intro v w hvw
    have hm : -v+w ∈ latticeSignGraph L χ := QuotientAddGroup.leftRel_apply.mp hvw
    obtain ⟨ω,hω,_⟩ := (latticeSignGraph_mem L χ (-v+w)).mp hm
    have he : w.1 = v.1+ω.1 := by
      change ω.1 = -v.1+w.1 at hω
      linear_combination -hω
    rw [he,periodTorusProjection_add_lattice L v.1 ω.1 ω.2])

@[simp] theorem latticeSignCoverProjection_mk (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (v : ℂ × ZMod 2) :
    latticeSignCoverProjection L χ (latticeSignCoverMk L χ v) = periodTorusProjection L v.1 := rfl

theorem latticeSignCoverProjection_isQuotientMap (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    IsQuotientMap (latticeSignCoverProjection L χ) := by
  apply (QuotientAddGroup.isQuotientMap_mk (latticeSignGraph L χ)).of_comp_isQuotientMap
  change IsQuotientMap (periodTorusProjection L ∘ Prod.fst)
  exact (QuotientAddGroup.isQuotientMap_mk L.lattice.toAddSubgroup).comp
    (isOpenMap_fst.isQuotientMap continuous_fst (fun z => ⟨(z,0),rfl⟩))

theorem latticeSignCover_t2 (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    T2Space (LatticeSignCover L χ) := inferInstance

noncomputable def latticeSignCoverDeck (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    LatticeSignCover L χ ≃ₜ LatticeSignCover L χ :=
  Homeomorph.addRight (latticeSignCoverMk L χ (0,1))

theorem latticeSignCoverDeck_mk (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (v : ℂ × ZMod 2) :
    latticeSignCoverDeck L χ (latticeSignCoverMk L χ v) =
      latticeSignCoverMk L χ (v.1,v.2+1) := by
  change (↑v : LatticeSignCover L χ)+↑((0,1) : ℂ × ZMod 2) = ↑((v.1,v.2+1) : ℂ × ZMod 2)
  rw [← QuotientAddGroup.mk_add]
  exact congrArg (latticeSignCoverMk L χ)
    (show v+(0,1) = (v.1,v.2+1) from Prod.ext (add_zero _) rfl)

theorem latticeSignCoverDeck_involutive (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    Function.Involutive (latticeSignCoverDeck L χ) := by
  intro q
  obtain ⟨v,rfl⟩ := Quotient.exists_rep q
  change latticeSignCoverDeck L χ (latticeSignCoverDeck L χ (latticeSignCoverMk L χ v)) = _
  rw [latticeSignCoverDeck_mk,latticeSignCoverDeck_mk]
  simp [latticeSignCoverMk,add_assoc,show (1 : ZMod 2)+1 = 0 from by decide]

theorem latticeSignCoverDeck_ne (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (q : LatticeSignCover L χ) : latticeSignCoverDeck L χ q ≠ q := by
  intro he
  have hv : latticeSignCoverMk L χ (0,1) = 0 := by
    change q+latticeSignCoverMk L χ (0,1) = q at he
    exact add_left_cancel (he.trans (add_zero q).symm)
  have hm := (QuotientAddGroup.eq_zero_iff (0,1)).mp hv
  obtain ⟨ω,hω,hχ⟩ := (latticeSignGraph_mem L χ (0,1)).mp hm
  have hω0 : ω = 0 := Subtype.ext hω
  rw [hω0,map_zero] at hχ
  exact zero_ne_one hχ

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.latticeSignCoverProjection_isQuotientMap
#print axioms TwoAxisHelicoid.latticeSignCoverDeck_ne

