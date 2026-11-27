module

public import TwoAxisHelicoid.VerticalAttachmentArithmetic

public section

namespace TwoAxisHelicoid.VerticalAttachment

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Both exact rational comparisons before decimal-grid rounding in the original
Machin calculation, at the finer precision used for the four printed sign tests. -/
theorem original_fine_machin_comparisons :
    VerticalRunCore.piLower ≤ 16*(atanBox (1/5)).1-4*(atanBox (1/239)).2 ∧
      16*(atanBox (1/5)).2-4*(atanBox (1/239)).1 ≤ VerticalRunCore.piUpper := by
  decide +kernel

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.original_fine_machin_comparisons
