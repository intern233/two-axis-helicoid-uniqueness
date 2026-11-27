import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfAdaptiveP438Rows
import TwoAxisHelicoid.PdfShortChordBatch442
import TwoAxisHelicoid.PdfShortChordBatch469

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows016 : List SignRow := (((adaptiveP438Rows ++ sharedDiskP442Rows) ++ (sharedDiskP461Rows ++ sharedDiskP466Rows)) ++ ((sharedDiskP469Rows ++ sharedDiskP473Rows) ++ (sharedDiskP476Rows ++ sharedDiskP479Rows)))
theorem positiveMomentCoverRows016_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows016 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append adaptiveP438Rows_actual sharedDiskP442Rows_actual) (original_horizontal_rows_append sharedDiskP461Rows_actual sharedDiskP466Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP469Rows_actual sharedDiskP473Rows_actual) (original_horizontal_rows_append sharedDiskP476Rows_actual sharedDiskP479Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows016_actual
