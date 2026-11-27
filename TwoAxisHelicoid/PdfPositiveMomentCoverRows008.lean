import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfAdaptiveP345Rows
import TwoAxisHelicoid.PdfAdaptiveP363Rows
import TwoAxisHelicoid.PdfAdaptiveP379Rows
import TwoAxisHelicoid.PdfAdaptiveP395Rows
import TwoAxisHelicoid.PdfAdaptiveP403Rows
import TwoAxisHelicoid.PdfAdaptiveP414Rows
import TwoAxisHelicoid.PdfSharedDiskP426Rows
import TwoAxisHelicoid.PdfShortChordBatch437

namespace TwoAxisHelicoid.PdfVertical
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open CertificateData CertificateSemantics

def positiveMomentCoverRows008 : List SignRow := (((adaptiveP345Rows ++ adaptiveP363Rows) ++ (adaptiveP379Rows ++ adaptiveP395Rows)) ++ ((adaptiveP403Rows ++ adaptiveP414Rows) ++ (sharedDiskP426Rows ++ sharedDiskP437Rows)))
theorem positiveMomentCoverRows008_actual : OriginalHorizontalRowsSound true positiveMomentCoverRows008 :=
  (original_horizontal_rows_append (original_horizontal_rows_append (original_horizontal_rows_append adaptiveP345Rows_actual adaptiveP363Rows_actual) (original_horizontal_rows_append adaptiveP379Rows_actual adaptiveP395Rows_actual)) (original_horizontal_rows_append (original_horizontal_rows_append adaptiveP403Rows_actual adaptiveP414Rows_actual) (original_horizontal_rows_append sharedDiskP426Rows_actual sharedDiskP437Rows_actual)))

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positiveMomentCoverRows008_actual
