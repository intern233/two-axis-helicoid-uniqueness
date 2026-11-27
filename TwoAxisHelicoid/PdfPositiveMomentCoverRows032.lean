import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfShortChordBatch493
import TwoAxisHelicoid.PdfShortChordBatch503
import TwoAxisHelicoid.PdfShortChordBatch511
import TwoAxisHelicoid.PdfShortChordBatch514

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows032 : List SignRow := (((sharedDiskP501Rows ++ sharedDiskP503Rows) ++ (sharedDiskP505Rows ++ sharedDiskP507Rows)) ++ ((sharedDiskP509Rows ++ sharedDiskP511Rows) ++ (sharedDiskP513Rows ++ sharedDiskP514Rows)))
theorem positiveMomentCoverRows032_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows032 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP501Rows_actual sharedDiskP503Rows_actual) (original_horizontal_rows_append sharedDiskP505Rows_actual sharedDiskP507Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP509Rows_actual sharedDiskP511Rows_actual) (original_horizontal_rows_append sharedDiskP513Rows_actual sharedDiskP514Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows032_actual
