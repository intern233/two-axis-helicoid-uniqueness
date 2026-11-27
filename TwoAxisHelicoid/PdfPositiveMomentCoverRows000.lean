import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfNodeRefinementsP079
import TwoAxisHelicoid.PdfAdaptiveP186Rows
import TwoAxisHelicoid.PdfChordGroupP225SourceRows
import TwoAxisHelicoid.PdfAdaptiveP265Rows
import TwoAxisHelicoid.PdfAdaptiveP273Rows
import TwoAxisHelicoid.PdfAdaptiveP296Rows
import TwoAxisHelicoid.PdfAdaptiveP313Rows
import TwoAxisHelicoid.PdfAdaptiveP329Rows

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows000 : List SignRow := (((originalNodeP079Rows ++ adaptiveP186Rows) ++ (meshP225SourceRows ++ adaptiveP265Rows)) ++ ((adaptiveP273Rows ++ adaptiveP296Rows) ++ (adaptiveP313Rows ++ adaptiveP329Rows)))
theorem positiveMomentCoverRows000_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows000 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append originalNodeP079Rows_actual adaptiveP186Rows_actual) (original_horizontal_rows_append meshP225SourceRows_actual adaptiveP265Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append adaptiveP273Rows_actual adaptiveP296Rows_actual) (original_horizontal_rows_append adaptiveP313Rows_actual adaptiveP329Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows000_actual
