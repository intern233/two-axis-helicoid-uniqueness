import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge20False : heatEdgeCheck heatStripT heatStripP 20 false := by decide +kernel
theorem heatStripEdge20True : heatEdgeCheck heatStripT heatStripP 20 true := by decide +kernel
theorem heatStripEdge21False : heatEdgeCheck heatStripT heatStripP 21 false := by decide +kernel
theorem heatStripEdge21True : heatEdgeCheck heatStripT heatStripP 21 true := by decide +kernel
theorem heatStripEdge22False : heatEdgeCheck heatStripT heatStripP 22 false := by decide +kernel
theorem heatStripEdge22True : heatEdgeCheck heatStripT heatStripP 22 true := by decide +kernel
theorem heatStripEdge23False : heatEdgeCheck heatStripT heatStripP 23 false := by decide +kernel
theorem heatStripEdge23True : heatEdgeCheck heatStripT heatStripP 23 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge23True
