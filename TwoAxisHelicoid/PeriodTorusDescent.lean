import TwoAxisHelicoid.RhombicLattice
import Mathlib.Topology.Covering.Quotient

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- The actual additive quotient of the complex plane by a period lattice. -/
abbrev PeriodTorus (L : PeriodPair) := ℂ ⧸ L.lattice.toAddSubgroup

abbrev PuncturedPeriodTorus (L : PeriodPair) := {q : PeriodTorus L // q ≠ 0}

def periodTorusProjection (L : PeriodPair) : ℂ → PeriodTorus L := QuotientAddGroup.mk

@[simp] theorem periodTorusProjection_eq_zero (L : PeriodPair) (z : ℂ) :
    periodTorusProjection L z = 0 ↔ z ∈ L.lattice :=
  QuotientAddGroup.eq_zero_iff z

/-- A function with genuine lattice periods descends to the quotient. -/
noncomputable def periodTorusLift {V : Type*} (L : PeriodPair) (F : ℂ → V)
    (hp : ∀ z ω, ω ∈ L.lattice → F (z+ω) = F z) : PeriodTorus L → V :=
  Quotient.lift F (by
    intro x y h
    have hm : -x+y ∈ L.lattice := QuotientAddGroup.leftRel_apply.mp h
    have he := hp x (-x+y) hm
    simpa only [add_neg_cancel_left] using he.symm)

@[simp] theorem periodTorusLift_projection {V : Type*} (L : PeriodPair) (F : ℂ → V)
    (hp : ∀ z ω, ω ∈ L.lattice → F (z+ω) = F z) (z : ℂ) :
    periodTorusLift L F hp (periodTorusProjection L z) = F z := rfl

theorem periodTorusLift_continuousAt {V : Type*} [TopologicalSpace V]
    (L : PeriodPair) (F : ℂ → V) (hp : ∀ z ω, ω ∈ L.lattice → F (z+ω) = F z)
    {z : ℂ} (hz : ContinuousAt F z) :
    ContinuousAt (periodTorusLift L F hp) (periodTorusProjection L z) := by
  exact QuotientAddGroup.isOpenQuotientMap_mk.continuousAt_comp_iff.mp hz

theorem periodTorusLift_continuous_punctured {V : Type*} [TopologicalSpace V]
    (L : PeriodPair) (F : ℂ → V) (hp : ∀ z ω, ω ∈ L.lattice → F (z+ω) = F z)
    (hF : ∀ z ∉ L.lattice, ContinuousAt F z) :
    Continuous (fun q : PuncturedPeriodTorus L => periodTorusLift L F hp q.1) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
  have hnot : z ∉ L.lattice := by
    intro h
    apply q.2
    rw [← hz]
    exact (periodTorusProjection_eq_zero L z).mpr h
  have hc := periodTorusLift_continuousAt L F hp (hF z hnot)
  have he : periodTorusProjection L z = q.1 := hz
  rw [he] at hc
  exact hc.comp continuous_subtype_val.continuousAt

theorem periodTorusProjection_isLocalHomeomorph (L : PeriodPair) :
    IsLocalHomeomorph (periodTorusProjection L) := by
  have hd : IsDiscrete (L.lattice.toAddSubgroup : Set ℂ) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology L.lattice))
  exact (L.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm hd).isLocalHomeomorph

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodTorusLift_continuous_punctured
#print axioms TwoAxisHelicoid.periodTorusProjection_isLocalHomeomorph
