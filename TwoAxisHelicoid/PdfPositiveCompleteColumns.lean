import TwoAxisHelicoid.PdfPositiveRowCoverageData
import TwoAxisHelicoid.PdfPositiveMomentCoverRows000
import TwoAxisHelicoid.PdfPositiveMomentCoverRows008
import TwoAxisHelicoid.PdfPositiveMomentCoverRows016
import TwoAxisHelicoid.PdfPositiveMomentCoverRows024
import TwoAxisHelicoid.PdfPositiveMomentCoverRows032
import TwoAxisHelicoid.PdfPositiveMomentCoverRows040
import TwoAxisHelicoid.PdfPositiveMomentCoverRows048
import TwoAxisHelicoid.PdfPositiveMomentCoverRows056
import TwoAxisHelicoid.PdfPositiveMomentCoverRows064
import TwoAxisHelicoid.PdfPositiveMomentCoverRows072
import TwoAxisHelicoid.PdfPositiveMomentCoverRows080

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def joinedPositiveDirect : List SignRow := (((positiveMomentCoverRows000 ++ positiveMomentCoverRows008) ++ (positiveMomentCoverRows016 ++ (positiveMomentCoverRows024 ++ positiveMomentCoverRows032))) ++ ((positiveMomentCoverRows040 ++ (positiveMomentCoverRows048 ++ positiveMomentCoverRows056)) ++ (positiveMomentCoverRows064 ++ (positiveMomentCoverRows072 ++ positiveMomentCoverRows080))))
theorem joinedPositiveDirect_actual : OriginalHorizontalRowsSound true joinedPositiveDirect :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append positiveMomentCoverRows000_actual positiveMomentCoverRows008_actual) (original_horizontal_rows_append positiveMomentCoverRows016_actual (original_horizontal_rows_append positiveMomentCoverRows024_actual positiveMomentCoverRows032_actual))) (original_horizontal_rows_append (original_horizontal_rows_append positiveMomentCoverRows040_actual (original_horizontal_rows_append positiveMomentCoverRows048_actual positiveMomentCoverRows056_actual)) (original_horizontal_rows_append positiveMomentCoverRows064_actual (original_horizontal_rows_append positiveMomentCoverRows072_actual positiveMomentCoverRows080_actual))))

/-- Each raw positive-table rectangle, including both boundary parameters,
satisfies both of the attachment's rational bounds on the actual complex integral. -/
theorem all_original_positive_horizontal_columns :
    OriginalHorizontalRowsSound true (positiveData.map CheckedSignRow.toSignRow) :=
  positive_original_rows_of_assignments (indices:=originalPositiveRowIndices) joinedPositiveDirect_actual
    (by change positiveRowAssignments originalSupplementalPositiveRows positiveData originalPositiveRowIndices=true
        exact original_positive_rows_have_checked_assignment)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.all_original_positive_horizontal_columns
