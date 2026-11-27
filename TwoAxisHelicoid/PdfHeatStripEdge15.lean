import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge60False : heatEdgeCheck heatStripT heatStripP 60 false := by decide +kernel
theorem heatStripEdge60True : heatEdgeCheck heatStripT heatStripP 60 true := by decide +kernel
theorem heatStripEdge61False : heatEdgeCheck heatStripT heatStripP 61 false := by decide +kernel
theorem heatStripEdge61True : heatEdgeCheck heatStripT heatStripP 61 true := by decide +kernel
theorem heatStripEdge62False : heatEdgeCheck heatStripT heatStripP 62 false := by decide +kernel
theorem heatStripEdge62True : heatEdgeCheck heatStripT heatStripP 62 true := by decide +kernel
theorem heatStripEdge63False : heatEdgeCheck heatStripT heatStripP 63 false := by decide +kernel
theorem heatStripEdge63True : heatEdgeCheck heatStripT heatStripP 63 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge63True
