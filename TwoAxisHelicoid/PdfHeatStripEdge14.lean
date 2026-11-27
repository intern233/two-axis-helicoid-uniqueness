import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge56False : heatEdgeCheck heatStripT heatStripP 56 false := by decide +kernel
theorem heatStripEdge56True : heatEdgeCheck heatStripT heatStripP 56 true := by decide +kernel
theorem heatStripEdge57False : heatEdgeCheck heatStripT heatStripP 57 false := by decide +kernel
theorem heatStripEdge57True : heatEdgeCheck heatStripT heatStripP 57 true := by decide +kernel
theorem heatStripEdge58False : heatEdgeCheck heatStripT heatStripP 58 false := by decide +kernel
theorem heatStripEdge58True : heatEdgeCheck heatStripT heatStripP 58 true := by decide +kernel
theorem heatStripEdge59False : heatEdgeCheck heatStripT heatStripP 59 false := by decide +kernel
theorem heatStripEdge59True : heatEdgeCheck heatStripT heatStripP 59 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge59True
