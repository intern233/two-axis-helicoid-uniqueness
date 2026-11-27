import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfShortChordBatch555

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows080 : List SignRow := (sharedDiskP555Rows ++ (sharedDiskP556Rows ++ sharedDiskP557Rows))
theorem positiveMomentCoverRows080_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows080 :=
  (original_horizontal_rows_append sharedDiskP555Rows_actual (original_horizontal_rows_append sharedDiskP556Rows_actual sharedDiskP557Rows_actual))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows080_actual
