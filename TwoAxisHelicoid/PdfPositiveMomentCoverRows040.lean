import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfShortChordBatch514
import TwoAxisHelicoid.PdfShortChordBatch518
import TwoAxisHelicoid.PdfSharedDiskP521Rows
import TwoAxisHelicoid.PdfSharedDiskP522Rows

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows040 : List SignRow := (((sharedDiskP515Rows ++ sharedDiskP516Rows) ++ (sharedDiskP517Rows ++ sharedDiskP518Rows)) ++ ((sharedDiskP519Rows ++ sharedDiskP520Rows) ++ (sharedDiskP521Rows ++ sharedDiskP522Rows)))
theorem positiveMomentCoverRows040_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows040 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP515Rows_actual sharedDiskP516Rows_actual) (original_horizontal_rows_append sharedDiskP517Rows_actual sharedDiskP518Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP519Rows_actual sharedDiskP520Rows_actual) (original_horizontal_rows_append sharedDiskP521Rows_actual sharedDiskP522Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows040_actual
