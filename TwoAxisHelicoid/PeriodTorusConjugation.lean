import TwoAxisHelicoid.PeriodTorusTopology

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ComplexConjugate

def ConjugationInvariantLattice (L : PeriodPair) : Prop :=
  ∀ z ∈ L.lattice, conj z ∈ L.lattice

theorem periodTorusProjection_eq_iff (L : PeriodPair) (z w : ℂ) :
    periodTorusProjection L z = periodTorusProjection L w ↔ w-z ∈ L.lattice := by
  change (QuotientAddGroup.mk z : PeriodTorus L) = QuotientAddGroup.mk w ↔ _
  rw [QuotientAddGroup.eq]
  simp only [sub_eq_add_neg,add_comm]
  rfl

noncomputable def periodTorusConjugation (L : PeriodPair) (hL : ConjugationInvariantLattice L) :
    PeriodTorus L → PeriodTorus L :=
  periodTorusLift L (fun z => periodTorusProjection L (conj z)) (by
    intro z ω hω
    rw [map_add,periodTorusProjection_add_lattice L _ _ (hL ω hω)])

@[simp] theorem periodTorusConjugation_projection (L : PeriodPair)
    (hL : ConjugationInvariantLattice L) (z : ℂ) :
    periodTorusConjugation L hL (periodTorusProjection L z) = periodTorusProjection L (conj z) := rfl

theorem periodTorusConjugation_involutive (L : PeriodPair) (hL : ConjugationInvariantLattice L) :
    Function.Involutive (periodTorusConjugation L hL) := by
  intro q
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  change periodTorusConjugation L hL (periodTorusConjugation L hL (periodTorusProjection L z)) =
    periodTorusProjection L z
  rw [periodTorusConjugation_projection,periodTorusConjugation_projection]
  simp

theorem periodTorusConjugation_continuous (L : PeriodPair) (hL : ConjugationInvariantLattice L) :
    Continuous (periodTorusConjugation L hL) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  exact periodTorusLift_continuousAt L _ _
    ((QuotientAddGroup.continuous_mk.comp Complex.continuous_conj).continuousAt)

theorem periodTorusConjugation_fixed_projection_iff (L : PeriodPair)
    (hL : ConjugationInvariantLattice L) (z : ℂ) :
    periodTorusConjugation L hL (periodTorusProjection L z) = periodTorusProjection L z ↔
      z-conj z ∈ L.lattice := by
  rw [periodTorusConjugation_projection,periodTorusProjection_eq_iff]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodTorusConjugation_continuous
