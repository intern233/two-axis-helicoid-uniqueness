module

public import TwoAxisHelicoid.VerticalDecimalBoxes
import all TwoAxisHelicoid.VerticalDecimalBoxes
public import TwoAxisHelicoid.VerticalMachinBounds
import Mathlib.Data.Rat.BigOperators

public section

namespace TwoAxisHelicoid.VerticalAttachment

theorem sumPrefix_cast_real (f : ℕ → ℚ) (n : ℕ) :
    ((VerticalRunCore.sumPrefix f n : ℚ) : ℝ) = ∑ j ∈ Finset.range n, (f j : ℝ) := by
  induction n with
  | zero => simp [VerticalRunCore.sumPrefix]
  | succ n ih => rw [VerticalRunCore.sumPrefix, Rat.cast_add, ih, Finset.sum_range_succ]

private theorem atan_endpoints (x : ℚ) :
    ((atanBox x).1 : ℝ) = atanSum40 (x : ℝ) ∧
      ((atanBox x).2 : ℝ) = atanSum40 (x : ℝ) + (x : ℝ)^81/81 := by
  simp [atanBox, sumPrefix_cast_real, atanSum40, atanTerm, mul_div_assoc]

/-- The unrounded rational enclosure implemented in the original attachment. -/
theorem uploaded_atan_box_contains {x : ℚ} (hx : 0 ≤ x) (hx1 : x < 1) :
    ContainsReal (atanBox x) (Real.arctan (x : ℝ)) := by
  have nonneg : 0 ≤ (x : ℝ) := by exact_mod_cast hx
  have small : (x : ℝ) < 1 := by exact_mod_cast hx1
  simpa only [ContainsReal, (atan_endpoints x).1, (atan_endpoints x).2]
    using atanSum40_bounds nonneg small

/-- The rounded 30-place interval computed by the uploaded Machin algorithm contains π. -/
theorem uploaded_machin_pi_contains : ContainsReal piBox Real.pi := by
  unfold piBox
  apply outward_contains_real
  · simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, (atan_endpoints _).1,
      (atan_endpoints _).2, Rat.cast_div, Rat.cast_one] using machin_unrounded_bounds.1
  · simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, (atan_endpoints _).1,
      (atan_endpoints _).2, Rat.cast_div, Rat.cast_one] using machin_unrounded_bounds.2

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.uploaded_atan_box_contains
#print axioms TwoAxisHelicoid.VerticalAttachment.uploaded_machin_pi_contains
