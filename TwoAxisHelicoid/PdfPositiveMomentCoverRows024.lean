import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfShortChordBatch482
import TwoAxisHelicoid.PdfRefinedP483Rows
import TwoAxisHelicoid.PdfSharedDiskP490Rows
import TwoAxisHelicoid.PdfShortChordBatch493

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows024 : List SignRow := (((sharedDiskP482Rows ++ refinedP483Rows) ++ (sharedDiskP484Rows ++ sharedDiskP487Rows)) ++ ((sharedDiskP490Rows ++ sharedDiskP493Rows) ++ (sharedDiskP496Rows ++ sharedDiskP499Rows)))
theorem positiveMomentCoverRows024_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows024 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP482Rows_actual refinedP483Rows_actual) (original_horizontal_rows_append sharedDiskP484Rows_actual sharedDiskP487Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP490Rows_actual sharedDiskP493Rows_actual) (original_horizontal_rows_append sharedDiskP496Rows_actual sharedDiskP499Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows024_actual
