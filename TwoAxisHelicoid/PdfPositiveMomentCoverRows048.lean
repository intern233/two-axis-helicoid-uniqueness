import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfShortChordBatch523
import TwoAxisHelicoid.PdfShortChordBatch527

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows048 : List SignRow := (((sharedDiskP523Rows ++ sharedDiskP524Rows) ++ (sharedDiskP525Rows ++ sharedDiskP526Rows)) ++ ((sharedDiskP527Rows ++ sharedDiskP528Rows) ++ (sharedDiskP529Rows ++ sharedDiskP530Rows)))
theorem positiveMomentCoverRows048_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows048 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP523Rows_actual sharedDiskP524Rows_actual) (original_horizontal_rows_append sharedDiskP525Rows_actual sharedDiskP526Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP527Rows_actual sharedDiskP528Rows_actual) (original_horizontal_rows_append sharedDiskP529Rows_actual sharedDiskP530Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows048_actual
