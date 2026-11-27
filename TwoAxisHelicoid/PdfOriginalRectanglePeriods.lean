import TwoAxisHelicoid.PdfRectanglePeriodRules
import TwoAxisHelicoid.OriginalPeriodBridge
import TwoAxisHelicoid.PdfPositiveCompleteColumns
import TwoAxisHelicoid.PdfOriginalPositivePeriodBridge
import TwoAxisHelicoid.PdfFactoredNegativeReported

namespace TwoAxisHelicoid.PdfVertical

/-- Re-evaluate the original sloping sigma contour with an independently
chosen abscissa at every point of all 617 uploaded rectangles. -/
theorem original_rectangle_periods :
    ReportedRectanglePeriods (fun t a => (originalSigmaPeriod t a).re) :=
  reported_rectangle_periods_of_columns thetaHorizontalPeriod
    (fun t a => (originalSigmaPeriod t a).re) originalSigmaPeriod_re_eq_horizontal
    (positive_table_period_of_columns all_original_positive_horizontal_columns)
    factored_negative_table_real

end TwoAxisHelicoid.PdfVertical

#print axioms TwoAxisHelicoid.PdfVertical.original_rectangle_periods
