module

public import Mathlib.Order.WithBot
public import Mathlib.Order.Bounds.Defs

public section
namespace TwoAxisHelicoid
open Set

/-- The recorded period is the least actual positive symmetry step, with
infinity used when the set of positive symmetry steps is empty. -/
def LeastPeriodOrInfinity {α : Type*} [LinearOrder α] (steps : Set α) (h : WithTop α) : Prop :=
  (h=⊤ ∧ steps=∅) ∨ ∃ p : α, h=(p : WithTop α) ∧ IsLeast steps p

theorem least_period_cutoff_iff {α : Type*} [LinearOrder α] {steps : Set α} {h : WithTop α}
    (record : LeastPeriodOrInfinity steps h) (η : α) :
    (η : WithTop α)≤h ↔ ∀ r∈steps, ¬r<η := by
  rcases record with ⟨rfl,rfl⟩ | ⟨p,rfl,least⟩
  · exact ⟨fun _ _ hr => False.elim hr,fun _ => le_top⟩
  · rw [WithTop.coe_le_coe]
    exact ⟨fun bound r hr => ((bound.trans (least.2 hr))).not_gt,
      fun no => le_of_not_gt (no p least.1)⟩

theorem least_period_finite_of_mem {α : Type*} [LinearOrder α] {steps : Set α} {h : WithTop α}
    (record : LeastPeriodOrInfinity steps h) (present : steps.Nonempty) :
    ∃ p : α, h=(p : WithTop α) ∧ IsLeast steps p := by
  rcases record with ⟨_,rfl⟩ | finite
  · obtain ⟨p,hp⟩ := present
    exact False.elim hp
  · exact finite

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.least_period_cutoff_iff
#print axioms TwoAxisHelicoid.least_period_finite_of_mem
