import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge32False : heatEdgeCheck heatStripT heatStripP 32 false := by decide +kernel
theorem heatStripEdge32True : heatEdgeCheck heatStripT heatStripP 32 true := by decide +kernel
theorem heatStripEdge33False : heatEdgeCheck heatStripT heatStripP 33 false := by decide +kernel
theorem heatStripEdge33True : heatEdgeCheck heatStripT heatStripP 33 true := by decide +kernel
theorem heatStripEdge34False : heatEdgeCheck heatStripT heatStripP 34 false := by decide +kernel
theorem heatStripEdge34True : heatEdgeCheck heatStripT heatStripP 34 true := by decide +kernel
theorem heatStripEdge35False : heatEdgeCheck heatStripT heatStripP 35 false := by decide +kernel
theorem heatStripEdge35True : heatEdgeCheck heatStripT heatStripP 35 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge35True
