import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# TwoAxisHelicoid: the integer arithmetic at the end of §4

These are conditional algebraic implications.  The geometric arguments giving
`|2*m - 1| ≤ 1` (Proposition 4.2) and `Odd m` (§4.5) are NOT proved here.
No statement in this file defines or classifies minimal surfaces or spin bundles.
-/

namespace TwoAxisHelicoid

/-- The arithmetic conclusion of Proposition 4.2, given its winding bound. -/
theorem integer_branch_candidates (m : ℤ) (h : |2 * m - 1| ≤ 1) :
    m = 0 ∨ m = 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  omega

/-- The conclusion of §4.5, given both independent geometric inputs. -/
theorem integer_branch_eq_one (m : ℤ) (hbound : |2 * m - 1| ≤ 1)
    (hodd : Odd m) : m = 1 := by
  obtain ⟨k, hk⟩ := hodd
  obtain hzero | hone := integer_branch_candidates m hbound
  · omega
  · exact hone

/-- The real-valued winding bound implies the corresponding integer bound. -/
theorem integer_winding_bound_of_real (m : ℤ)
    (h : |2 * (m : ℝ) - 1| ≤ 1) : |2 * m - 1| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  apply abs_le.mpr
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- The same conditional branch selection with the bound expressed in ℝ. -/
theorem real_winding_branch_eq_one (m : ℤ)
    (hbound : |2 * (m : ℝ) - 1| ≤ 1) (hodd : Odd m) : m = 1 := by
  exact integer_branch_eq_one m (integer_winding_bound_of_real m hbound) hodd

/-- Equivalence useful for checking that the permitted branch is not lost. -/
theorem integer_branch_iff (m : ℤ) :
    (|2 * m - 1| ≤ 1 ∧ Odd m) ↔ m = 1 := by
  constructor
  · rintro ⟨hbound, hodd⟩
    exact integer_branch_eq_one m hbound hodd
  · rintro rfl
    norm_num

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.integer_branch_candidates
#print axioms TwoAxisHelicoid.integer_branch_eq_one
#print axioms TwoAxisHelicoid.integer_winding_bound_of_real
#print axioms TwoAxisHelicoid.real_winding_branch_eq_one
#print axioms TwoAxisHelicoid.integer_branch_iff
