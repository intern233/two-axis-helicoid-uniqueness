import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge52False : heatEdgeCheck heatStripT heatStripP 52 false := by decide +kernel
theorem heatStripEdge52True : heatEdgeCheck heatStripT heatStripP 52 true := by decide +kernel
theorem heatStripEdge53False : heatEdgeCheck heatStripT heatStripP 53 false := by decide +kernel
theorem heatStripEdge53True : heatEdgeCheck heatStripT heatStripP 53 true := by decide +kernel
theorem heatStripEdge54False : heatEdgeCheck heatStripT heatStripP 54 false := by decide +kernel
theorem heatStripEdge54True : heatEdgeCheck heatStripT heatStripP 54 true := by decide +kernel
theorem heatStripEdge55False : heatEdgeCheck heatStripT heatStripP 55 false := by decide +kernel
theorem heatStripEdge55True : heatEdgeCheck heatStripT heatStripP 55 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge55True
