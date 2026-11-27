import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfShortChordBatch547
import TwoAxisHelicoid.PdfShortChordBatch551

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows072 : List SignRow := (((sharedDiskP547Rows ++ sharedDiskP548Rows) ++ (sharedDiskP549Rows ++ sharedDiskP550Rows)) ++ ((sharedDiskP551Rows ++ sharedDiskP552Rows) ++ (sharedDiskP553Rows ++ sharedDiskP554Rows)))
theorem positiveMomentCoverRows072_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows072 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP547Rows_actual sharedDiskP548Rows_actual) (original_horizontal_rows_append sharedDiskP549Rows_actual sharedDiskP550Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append sharedDiskP551Rows_actual sharedDiskP552Rows_actual) (original_horizontal_rows_append sharedDiskP553Rows_actual sharedDiskP554Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows072_actual
