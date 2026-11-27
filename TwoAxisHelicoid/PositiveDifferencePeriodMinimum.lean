module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section
namespace TwoAxisHelicoid
open Set

/-- A nonempty set of times separated from zero, containing the positive
differences of its members, contains its infimum. In particular the
cutoff gives a minimum without a closedness assumption. -/
theorem positive_difference_period_minimum {A : Type*} [AddCommGroup A] [ConditionallyCompleteLinearOrder A]
    [IsOrderedAddMonoid A] {P : Set A} {η : A} (pos : 0<η)
    (present : P.Nonempty) (lower : ∀ t∈P, η≤t)
    (subtract : ∀ {s t : A}, s∈P → t∈P → s<t → t-s∈P) : IsLeast P (sInf P) := by
  have bounded : BddBelow P := ⟨η,lower⟩
  obtain ⟨r,hr,near⟩ := exists_lt_of_csInf_lt present (lt_add_of_pos_right (sInf P) pos)
  have least : IsLeast P r := by
    refine ⟨hr,?_⟩
    intro s hs
    apply le_of_not_gt
    intro less
    have sep := lower (r-s) (subtract hs hr less)
    have low := csInf_le bounded hs
    have upper : r<s+η := near.trans_le (add_le_add low le_rfl)
    exact (not_le_of_gt ((sub_lt_iff_lt_add').mpr upper)) sep
  exact least.csInf_eq.symm ▸ least

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positive_difference_period_minimum
