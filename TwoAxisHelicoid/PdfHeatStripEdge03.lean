import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge12False : heatEdgeCheck heatStripT heatStripP 12 false := by decide +kernel
theorem heatStripEdge12True : heatEdgeCheck heatStripT heatStripP 12 true := by decide +kernel
theorem heatStripEdge13False : heatEdgeCheck heatStripT heatStripP 13 false := by decide +kernel
theorem heatStripEdge13True : heatEdgeCheck heatStripT heatStripP 13 true := by decide +kernel
theorem heatStripEdge14False : heatEdgeCheck heatStripT heatStripP 14 false := by decide +kernel
theorem heatStripEdge14True : heatEdgeCheck heatStripT heatStripP 14 true := by decide +kernel
theorem heatStripEdge15False : heatEdgeCheck heatStripT heatStripP 15 false := by decide +kernel
theorem heatStripEdge15True : heatEdgeCheck heatStripT heatStripP 15 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge15True
