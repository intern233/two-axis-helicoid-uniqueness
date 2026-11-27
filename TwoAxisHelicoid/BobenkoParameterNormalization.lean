module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section
namespace TwoAxisHelicoid
open Set

/-- The TwoAxisHelicoid interval is exactly the physical length range above the first
exceptional midpoint in Bobenko's even characteristic. -/
theorem bobenko_length_admissible_iff {L : ℝ} (hL : 0 < L) :
    1-1/(2*L) ∈ Ioo (0:ℝ) 1 ↔ 1/2 < L := by
  have pos : 0 < 2*L := mul_pos (by norm_num) hL
  have reciprocal : 0 < 1/(2*L) := div_pos zero_lt_one pos
  constructor
  · intro h
    have bound : 1/(2*L) < 1 := by linarith [h.1]
    have scaled := (div_lt_iff₀ pos).mp bound
    linarith
  · intro half
    have bound : 1/(2*L) < 1 := (div_lt_iff₀ pos).mpr (by linarith)
    exact ⟨by linarith,by linarith⟩

/-- The two printed parameter relations are inverses throughout the original interval. -/
theorem bobenko_admissible_length_inverse {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) :
    let L := 1/(2*(1-a))
    1/2 < L ∧ a = 1-1/(2*L) ∧ ∀ L' : ℝ, a = 1-1/(2*L') → L' = L := by
  intro L
  have gap : 0 < 1-a := sub_pos.mpr ha.2
  have positive : 0 < L := div_pos zero_lt_one (mul_pos (by norm_num) gap)
  have twice : 2*L = (1-a)⁻¹ := by
    dsimp [L]
    field_simp [gap.ne']
  have relation : a = 1-1/(2*L) := by rw [twice,one_div,inv_inv]; ring
  have admissible : 1-1/(2*L) ∈ Ioo (0:ℝ) 1 := by rwa [← relation]
  refine ⟨(bobenko_length_admissible_iff positive).mp admissible,relation,?_⟩
  intro L' formula
  have nonzero : L' ≠ 0 := by
    rintro rfl
    norm_num at formula
    exact ha.2.ne formula
  have reciprocal : 1-a = 1/(2*L') := by linarith [formula]
  have product := (eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) nonzero)).mp reciprocal
  change L' = 1/(2*(1-a))
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) gap.ne')).mpr
  calc L'*(2*(1-a)) = (1-a)*(2*L') := by ring
       _ = 1 := product

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.bobenko_length_admissible_iff
#print axioms TwoAxisHelicoid.bobenko_admissible_length_inverse
