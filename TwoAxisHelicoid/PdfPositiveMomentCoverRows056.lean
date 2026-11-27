import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfShortChordBatch531
import TwoAxisHelicoid.PdfShortChordBatch535

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows056 : List SignRow := (((sharedDiskP531Rows ++ sharedDiskP532Rows) ++ (sharedDiskP533Rows ++ sharedDiskP534Rows)) ++ ((sharedDiskP535Rows ++ sharedDiskP536Rows) ++ (sharedDiskP537Rows ++ sharedDiskP538Rows)))
theorem positiveMomentCoverRows056_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows056 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP531Rows_actual sharedDiskP532Rows_actual) (original_horizontal_rows_append sharedDiskP533Rows_actual sharedDiskP534Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP535Rows_actual sharedDiskP536Rows_actual) (original_horizontal_rows_append sharedDiskP537Rows_actual sharedDiskP538Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows056_actual
