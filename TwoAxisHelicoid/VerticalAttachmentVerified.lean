import TwoAxisHelicoid.VerticalAttachmentRawTests
import TwoAxisHelicoid.VerticalAttachmentSlope
import TwoAxisHelicoid.VerticalRunDisplayedEndpoints
import TwoAxisHelicoid.VerticalRunPrintedSlope

namespace TwoAxisHelicoid.VerticalAttachment

private theorem actual_F_inside {t lo hi : ℚ} (ht : 0 < t) (hl : 0 ≤ lo) (hh : hi < 1)
    (tests : VerticalRunCore.Tests t lo hi (normalizedF t).1 (normalizedF t).2) :
    ((normalizedF t).1 : ℝ) < ellipticFReal (t : ℝ)/Real.pi^2 ∧
      ellipticFReal (t : ℝ)/Real.pi^2 < ((normalizedF t).2 : ℝ) := by
  obtain ⟨exponential, series⟩ := VerticalRun.tests_of_core tests
  exact VerticalRun.displayed_bound_of_tests ht hl hh exponential series

/-- Both exact rational output intervals of normalized_F_bounds contain the
actual half-period function before the attachment formats its decimal log. -/
theorem uploaded_normalized_F_enclosures :
    (((normalizedF left).1 : ℝ) < ellipticFReal (left : ℝ)/Real.pi^2 ∧
      ellipticFReal (left : ℝ)/Real.pi^2 < ((normalizedF left).2 : ℝ)) ∧
    (((normalizedF right).1 : ℝ) < ellipticFReal (right : ℝ)/Real.pi^2 ∧
      ellipticFReal (right : ℝ)/Real.pi^2 < ((normalizedF right).2 : ℝ)) := by
  constructor
  · exact actual_F_inside (by decide +kernel) (by decide +kernel) (by decide +kernel) left_raw_tests
  · exact actual_F_inside (by decide +kernel) (by decide +kernel) (by decide +kernel) right_raw_tests

/-- The exact output of the attachment's Lambert calculation contains the
one-sided derivative of the actual endpoint extension. -/
theorem uploaded_slope_enclosure :
    (slopeBox.1 : ℝ) < derivWithin rightExtendedPeriod (Set.Iio ellipticVerticalUpper) ellipticVerticalUpper ∧
    derivWithin rightExtendedPeriod (Set.Iio ellipticVerticalUpper) ellipticVerticalUpper < (slopeBox.2 : ℝ) := by
  rw [original_slope_log_arithmetic.1]
  convert vertical_run_displayed_right_derivative using 2 <;>
    norm_num [numeratorBox, decimalScale]

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.uploaded_normalized_F_enclosures
#print axioms TwoAxisHelicoid.VerticalAttachment.uploaded_slope_enclosure
