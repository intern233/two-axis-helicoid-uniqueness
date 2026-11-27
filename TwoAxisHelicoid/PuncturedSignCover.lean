import TwoAxisHelicoid.LatticeSignDoubleCover
import TwoAxisHelicoid.PuncturedLatticePlane

namespace TwoAxisHelicoid
open Set Topology

abbrev PuncturedSignCover (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :=
  {q : LatticeSignCover L χ // latticeSignCoverProjection L χ q ≠ 0}

noncomputable def puncturedSignCoverProjection (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    PuncturedSignCover L χ → PuncturedPeriodTorus L :=
  fun q => ⟨latticeSignCoverProjection L χ q.1,q.2⟩

theorem puncturedSignCoverProjection_continuous (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    Continuous (puncturedSignCoverProjection L χ) :=
  ((latticeSignCoverProjection_isQuotientMap L χ).continuous.comp continuous_subtype_val).subtype_mk _

theorem puncturedSignCover_open (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    IsOpen {q : LatticeSignCover L χ | latticeSignCoverProjection L χ q ≠ 0} := by
  let : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  exact isOpen_ne_fun (latticeSignCoverProjection_isQuotientMap L χ).continuous continuous_const

theorem puncturedSignCoverProjection_isLocalHomeomorph (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    IsLocalHomeomorph (puncturedSignCoverProjection L χ) := by
  let : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  have hdom : IsOpenEmbedding (Subtype.val : PuncturedSignCover L χ → LatticeSignCover L χ) :=
    (puncturedSignCover_open L χ).isOpenEmbedding_subtypeVal
  have hcod : IsOpenEmbedding (Subtype.val : PuncturedPeriodTorus L → PeriodTorus L) :=
    isOpen_ne.isOpenEmbedding_subtypeVal
  have hh := (latticeSignCoverProjection_isCoveringMap L χ).isLocalHomeomorph.comp hdom.isLocalHomeomorph
  change IsLocalHomeomorph ((Subtype.val : PuncturedPeriodTorus L → PeriodTorus L) ∘
    puncturedSignCoverProjection L χ) at hh
  exact hh.of_comp hcod.isLocalHomeomorph (puncturedSignCoverProjection_continuous L χ)

noncomputable def puncturedSignCoverMk (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    PuncturedLatticePlane L × ZMod 2 → PuncturedSignCover L χ :=
  fun v => ⟨latticeSignCoverMk L χ (v.1.1,v.2),by
    rw [latticeSignCoverProjection_mk]
    exact fun h => v.1.2 ((periodTorusProjection_eq_zero L v.1.1).mp h)⟩

theorem puncturedSignCoverMk_continuous (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    Continuous (puncturedSignCoverMk L χ) := by
  apply Continuous.subtype_mk
  exact QuotientAddGroup.continuous_mk.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem puncturedSignCoverMk_surjective (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    Function.Surjective (puncturedSignCoverMk L χ) := by
  intro q
  obtain ⟨v,hv⟩ := Quotient.exists_rep q.1
  have hn : v.1 ∉ L.lattice := by
    intro h
    apply q.2
    rw [← hv]
    exact (periodTorusProjection_eq_zero L v.1).mpr h
  exact ⟨(⟨v.1,hn⟩,v.2),Subtype.ext hv⟩

theorem puncturedSignCoverMk_isLocalHomeomorph (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    IsLocalHomeomorph (puncturedSignCoverMk L χ) := by
  have hi : IsOpenEmbedding (Prod.map (Subtype.val : PuncturedLatticePlane L → ℂ) (id : ZMod 2 → ZMod 2)) :=
    L.isClosed_lattice.isOpen_compl.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
  have ho : IsOpenEmbedding (Subtype.val : PuncturedSignCover L χ → LatticeSignCover L χ) :=
    (puncturedSignCover_open L χ).isOpenEmbedding_subtypeVal
  have hh := (latticeSignCoverMk_isLocalHomeomorph L χ).comp hi.isLocalHomeomorph
  change IsLocalHomeomorph ((Subtype.val : PuncturedSignCover L χ → LatticeSignCover L χ) ∘
    puncturedSignCoverMk L χ) at hh
  exact hh.of_comp ho.isLocalHomeomorph (puncturedSignCoverMk_continuous L χ)

theorem puncturedSignCoverMk_isQuotientMap (L : PeriodPair) (χ : L.lattice →+ ZMod 2) :
    IsQuotientMap (puncturedSignCoverMk L χ) :=
  (puncturedSignCoverMk_isLocalHomeomorph L χ).isOpenMap.isQuotientMap
    (puncturedSignCoverMk_continuous L χ) (puncturedSignCoverMk_surjective L χ)

theorem puncturedSignCoverMk_eq (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (v w : PuncturedLatticePlane L × ZMod 2) :
    puncturedSignCoverMk L χ v = puncturedSignCoverMk L χ w ↔
      ∃ ω : L.lattice, v.1.1-w.1.1 = ω.1 ∧ v.2-w.2 = χ ω := by
  rw [Subtype.ext_iff]
  exact latticeSignCoverMk_eq L χ (v.1.1,v.2) (w.1.1,w.2)

@[simp] theorem puncturedSignCoverProjection_mk (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (v : PuncturedLatticePlane L × ZMod 2) :
    puncturedSignCoverProjection L χ (puncturedSignCoverMk L χ v) =
      puncturedPlaneProjection L v.1 := rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.puncturedSignCoverMk_isQuotientMap

