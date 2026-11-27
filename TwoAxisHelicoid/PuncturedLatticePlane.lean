import TwoAxisHelicoid.PeriodTorusTopology

namespace TwoAxisHelicoid
open Set Topology

abbrev PuncturedLatticePlane (L : PeriodPair) := {z : ℂ // z ∉ L.lattice}

def puncturedPlaneProjection (L : PeriodPair) :
    PuncturedLatticePlane L → PuncturedPeriodTorus L :=
  fun z => ⟨periodTorusProjection L z.1,fun h => z.2 ((periodTorusProjection_eq_zero L z.1).mp h)⟩

theorem puncturedPlaneProjection_continuous (L : PeriodPair) :
    Continuous (puncturedPlaneProjection L) :=
  (QuotientAddGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _

theorem puncturedPlaneProjection_surjective (L : PeriodPair) :
    Function.Surjective (puncturedPlaneProjection L) := by
  intro q
  obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
  have hn : z ∉ L.lattice := by
    intro h
    exact q.2 (hz ▸ (periodTorusProjection_eq_zero L z).mpr h)
  exact ⟨⟨z,hn⟩,Subtype.ext hz⟩

theorem puncturedPlaneProjection_isLocalHomeomorph (L : PeriodPair) :
    IsLocalHomeomorph (puncturedPlaneProjection L) := by
  let : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  have hdom : IsOpenEmbedding (Subtype.val : PuncturedLatticePlane L → ℂ) :=
    L.isClosed_lattice.isOpen_compl.isOpenEmbedding_subtypeVal
  have hcod : IsOpenEmbedding (Subtype.val : PuncturedPeriodTorus L → PeriodTorus L) :=
    isOpen_ne.isOpenEmbedding_subtypeVal
  have hh := (periodTorusProjection_isLocalHomeomorph L).comp hdom.isLocalHomeomorph
  change IsLocalHomeomorph ((Subtype.val : PuncturedPeriodTorus L → PeriodTorus L) ∘
    puncturedPlaneProjection L) at hh
  exact hh.of_comp hcod.isLocalHomeomorph (puncturedPlaneProjection_continuous L)

theorem puncturedPlaneProjection_isQuotientMap (L : PeriodPair) :
    IsQuotientMap (puncturedPlaneProjection L) :=
  (puncturedPlaneProjection_isLocalHomeomorph L).isOpenMap.isQuotientMap
    (puncturedPlaneProjection_continuous L) (puncturedPlaneProjection_surjective L)

theorem puncturedPlaneProjection_eq_iff (L : PeriodPair) (z w : PuncturedLatticePlane L) :
    puncturedPlaneProjection L z = puncturedPlaneProjection L w ↔ z.1-w.1 ∈ L.lattice := by
  rw [Subtype.ext_iff]
  exact QuotientAddGroup.eq_iff_sub_mem

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.puncturedPlaneProjection_isLocalHomeomorph

