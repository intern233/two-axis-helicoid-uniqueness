import TwoAxisHelicoid.PeriodTorusDescent
import Mathlib.Analysis.Normed.Module.Connected

namespace TwoAxisHelicoid
open Complex Set Topology

theorem periodTorusProjection_add_lattice (L : PeriodPair) (z ω : ℂ) (hω : ω ∈ L.lattice) :
    periodTorusProjection L (z+ω) = periodTorusProjection L z := by
  change (↑(z+ω) : PeriodTorus L) = ↑z
  rw [QuotientAddGroup.mk_add,(QuotientAddGroup.eq_zero_iff ω).mpr hω,add_zero]

theorem periodTorus_compactSpace (L : PeriodPair) : CompactSpace (PeriodTorus L) := by
  have hc := IsZLattice.isCompact_range_of_periodic L.lattice (periodTorusProjection L)
    QuotientAddGroup.continuous_mk (periodTorusProjection_add_lattice L)
  have hs : Function.Surjective (periodTorusProjection L) := Quotient.mk_surjective
  rw [hs.range_eq] at hc
  exact isCompact_univ_iff.mp hc

theorem periodTorus_punctured_isConnected (L : PeriodPair) :
    IsConnected {q : PeriodTorus L | q ≠ 0} := by
  have hc : IsConnected ((L.lattice : Set ℂ)ᶜ) :=
    Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))
  have he : periodTorusProjection L '' (L.lattice : Set ℂ)ᶜ = {q : PeriodTorus L | q ≠ 0} := by
    ext q
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact fun h => hz ((periodTorusProjection_eq_zero L z).mp h)
    · intro hq
      obtain ⟨z,rfl⟩ := Quotient.exists_rep q
      refine ⟨z,?_,rfl⟩
      intro hz
      exact hq ((periodTorusProjection_eq_zero L z).mpr hz)
  rw [← he]
  exact hc.image _ QuotientAddGroup.continuous_mk.continuousOn

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodTorus_compactSpace
#print axioms TwoAxisHelicoid.periodTorus_punctured_isConnected
