import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge24False : heatEdgeCheck heatStripT heatStripP 24 false := by decide +kernel
theorem heatStripEdge24True : heatEdgeCheck heatStripT heatStripP 24 true := by decide +kernel
theorem heatStripEdge25False : heatEdgeCheck heatStripT heatStripP 25 false := by decide +kernel
theorem heatStripEdge25True : heatEdgeCheck heatStripT heatStripP 25 true := by decide +kernel
theorem heatStripEdge26False : heatEdgeCheck heatStripT heatStripP 26 false := by decide +kernel
theorem heatStripEdge26True : heatEdgeCheck heatStripT heatStripP 26 true := by decide +kernel
theorem heatStripEdge27False : heatEdgeCheck heatStripT heatStripP 27 false := by decide +kernel
theorem heatStripEdge27True : heatEdgeCheck heatStripT heatStripP 27 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge27True
