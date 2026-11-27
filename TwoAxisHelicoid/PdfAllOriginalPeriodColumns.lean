import TwoAxisHelicoid.PdfAllVerticalAttachments
import TwoAxisHelicoid.PdfPositiveCompleteColumns
import TwoAxisHelicoid.PdfOriginalPositivePeriodBridge
import TwoAxisHelicoid.PdfFactoredNegativeReported
import TwoAxisHelicoid.PdfFactoredHeatReported
import TwoAxisHelicoid.PdfEndpointHorizontalReported
import TwoAxisHelicoid.CompactRootLeftReported
import TwoAxisHelicoid.CompactRootRightReported

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics

/-- The original positive and negative complex periods on complete rectangles,
the heat derivative on its actual branch, and the ten right-end upper bounds. -/
theorem original_period_column_tables :
    OriginalHorizontalRowsSound true (positiveData.map CheckedSignRow.toSignRow) ∧
    (∀ r∈positiveData, ∀ t : ℝ, RealMem r.t t →
      RealMem r.hReal (actualPeriodAlong t) ∧ 3/10000<actualPeriodAlong t) ∧
    (∀ r∈negativeData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (pdfPrimalHorizontalIntegral t a).re ∧
      RealMem r.hImag (pdfPrimalHorizontalIntegral t a).im) ∧
    (∀ r∈derivativeData, ∀ t : ℝ, RealMem r.t t →
      deriv actualPeriodAlong t≤(r.hPrimeUpper:ℝ)) ∧
    ∀ r∈endpointData, ∀ t a : ℝ, (7/5:ℝ)≤t → t≤141/100 →
      RealMem r.a a → thetaHorizontalPeriod t a≤(r.hUpper:ℝ) :=
  ⟨all_original_positive_horizontal_columns,
    positive_table_branch_of_columns all_original_positive_horizontal_columns positive_actual_abscissa_in_reported_interval,
    factored_negative_table_horizontal_columns, factored_derivative_table_sharp_upper,
    original_endpoint_ten_horizontal_upper_bounds⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_period_column_tables

