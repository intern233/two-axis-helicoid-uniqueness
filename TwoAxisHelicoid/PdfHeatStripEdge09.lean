import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge36False : heatEdgeCheck heatStripT heatStripP 36 false := by decide +kernel
theorem heatStripEdge36True : heatEdgeCheck heatStripT heatStripP 36 true := by decide +kernel
theorem heatStripEdge37False : heatEdgeCheck heatStripT heatStripP 37 false := by decide +kernel
theorem heatStripEdge37True : heatEdgeCheck heatStripT heatStripP 37 true := by decide +kernel
theorem heatStripEdge38False : heatEdgeCheck heatStripT heatStripP 38 false := by decide +kernel
theorem heatStripEdge38True : heatEdgeCheck heatStripT heatStripP 38 true := by decide +kernel
theorem heatStripEdge39False : heatEdgeCheck heatStripT heatStripP 39 false := by decide +kernel
theorem heatStripEdge39True : heatEdgeCheck heatStripT heatStripP 39 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge39True
