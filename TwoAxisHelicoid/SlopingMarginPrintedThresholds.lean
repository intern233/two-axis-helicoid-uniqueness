module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Rat.Cast.Order

public section
namespace TwoAxisHelicoid.SlopingMarginKernel
open Set

/-- Compare the positive table's exact extremal entry with the printed strict threshold. -/
theorem positivePrintedThreshold :
    (3/10000 : ℝ) <
      ((4048815533235523741519408834611/10384593717069655257060992658440192 : ℚ) : ℝ) := by
  have h : (3/10000 : ℚ) <
      4048815533235523741519408834611/10384593717069655257060992658440192 := by decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).2 h

/-- The absolute margin of the negative table strictly exceeds one twenty-fifth. -/
theorem negativePrintedThreshold :
    (1/25 : ℝ) <
      ((238070159187588210339310175778799/5192296858534827628530496329220096 : ℚ) : ℝ) := by
  have h : (1/25 : ℚ) <
      238070159187588210339310175778799/5192296858534827628530496329220096 := by decide +kernel
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).2 h

theorem strictBoundsOfExactMargins (F : ℝ → ℝ)
    (bounds : (∀ t ∈ Icc (1/8 : ℝ) (17/20),
      ((4048815533235523741519408834611/10384593717069655257060992658440192 : ℚ) : ℝ) ≤ F t) ∧
      ∀ t ∈ Icc (9/10 : ℝ) (7/5),
        F t ≤ -((238070159187588210339310175778799/5192296858534827628530496329220096 : ℚ) : ℝ)) :
    (∀ t ∈ Icc (1/8 : ℝ) (17/20), 3/10000 < F t) ∧
      ∀ t ∈ Icc (9/10 : ℝ) (7/5), F t < -(1/25 : ℝ) :=
  ⟨fun t ht => positivePrintedThreshold.trans_le (bounds.1 t ht),
   fun t ht => (bounds.2 t ht).trans_lt (neg_lt_neg negativePrintedThreshold)⟩

end TwoAxisHelicoid.SlopingMarginKernel

#print axioms TwoAxisHelicoid.SlopingMarginKernel.positivePrintedThreshold
#print axioms TwoAxisHelicoid.SlopingMarginKernel.negativePrintedThreshold
#print axioms TwoAxisHelicoid.SlopingMarginKernel.strictBoundsOfExactMargins
