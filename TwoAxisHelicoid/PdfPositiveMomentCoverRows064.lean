import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfShortChordBatch539
import TwoAxisHelicoid.PdfShortChordBatch543

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows064 : List SignRow := (((sharedDiskP539Rows ++ sharedDiskP540Rows) ++ (sharedDiskP541Rows ++ sharedDiskP542Rows)) ++ ((sharedDiskP543Rows ++ sharedDiskP544Rows) ++ (sharedDiskP545Rows ++ sharedDiskP546Rows)))
theorem positiveMomentCoverRows064_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows064 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP539Rows_actual sharedDiskP540Rows_actual) (original_horizontal_rows_append sharedDiskP541Rows_actual sharedDiskP542Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP543Rows_actual sharedDiskP544Rows_actual) (original_horizontal_rows_append sharedDiskP545Rows_actual sharedDiskP546Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows064_actual
