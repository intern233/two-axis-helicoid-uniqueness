module

public import TwoAxisHelicoid.VerticalAttachmentPi
import all TwoAxisHelicoid.VerticalDecimalBoxes
public import TwoAxisHelicoid.VerticalFineMachinArithmetic
import Mathlib.Tactic.Linarith

public section

namespace TwoAxisHelicoid.VerticalAttachment

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Before rounding to the upload's 30-place grid, its same two 40-term
arctangent sums certify both 41-place π bounds used in the finer tests. -/
theorem uploaded_machin_fine_pi :
    (VerticalRunCore.piLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (VerticalRunCore.piUpper : ℝ) := by
  let a := atanBox (1/5)
  let b := atanBox (1/239)
  have ha : ContainsReal a (Real.arctan (1/5)) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, a] using
      (uploaded_atan_box_contains (x := 1/5) (by decide +kernel) (by decide +kernel))
  have hb : ContainsReal b (Real.arctan (1/239)) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, b] using
      (uploaded_atan_box_contains (x := 1/239) (by decide +kernel) (by decide +kernel))
  have low : VerticalRunCore.piLower ≤ 16*a.1-4*b.2 := original_fine_machin_comparisons.1
  have high : 16*a.2-4*b.1 ≤ VerticalRunCore.piUpper := original_fine_machin_comparisons.2
  have lo : (VerticalRunCore.piLower : ℝ) ≤ 16*(a.1 : ℝ)-4*(b.2 : ℝ) := by exact_mod_cast low
  have hi : 16*(a.2 : ℝ)-4*(b.1 : ℝ) ≤ (VerticalRunCore.piUpper : ℝ) := by exact_mod_cast high
  have h : 4*Real.arctan (1/5) - Real.arctan (1/239) = Real.pi/4 := by
    simpa only [one_div] using Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.uploaded_machin_fine_pi
