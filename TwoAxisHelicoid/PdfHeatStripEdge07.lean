import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge28False : heatEdgeCheck heatStripT heatStripP 28 false := by decide +kernel
theorem heatStripEdge28True : heatEdgeCheck heatStripT heatStripP 28 true := by decide +kernel
theorem heatStripEdge29False : heatEdgeCheck heatStripT heatStripP 29 false := by decide +kernel
theorem heatStripEdge29True : heatEdgeCheck heatStripT heatStripP 29 true := by decide +kernel
theorem heatStripEdge30False : heatEdgeCheck heatStripT heatStripP 30 false := by decide +kernel
theorem heatStripEdge30True : heatEdgeCheck heatStripT heatStripP 30 true := by decide +kernel
theorem heatStripEdge31False : heatEdgeCheck heatStripT heatStripP 31 false := by decide +kernel
theorem heatStripEdge31True : heatEdgeCheck heatStripT heatStripP 31 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge31True
