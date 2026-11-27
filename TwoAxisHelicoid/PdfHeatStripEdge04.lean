import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge16False : heatEdgeCheck heatStripT heatStripP 16 false := by decide +kernel
theorem heatStripEdge16True : heatEdgeCheck heatStripT heatStripP 16 true := by decide +kernel
theorem heatStripEdge17False : heatEdgeCheck heatStripT heatStripP 17 false := by decide +kernel
theorem heatStripEdge17True : heatEdgeCheck heatStripT heatStripP 17 true := by decide +kernel
theorem heatStripEdge18False : heatEdgeCheck heatStripT heatStripP 18 false := by decide +kernel
theorem heatStripEdge18True : heatEdgeCheck heatStripT heatStripP 18 true := by decide +kernel
theorem heatStripEdge19False : heatEdgeCheck heatStripT heatStripP 19 false := by decide +kernel
theorem heatStripEdge19True : heatEdgeCheck heatStripT heatStripP 19 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge19True
