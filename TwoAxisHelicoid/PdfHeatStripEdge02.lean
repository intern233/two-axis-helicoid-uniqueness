import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge08False : heatEdgeCheck heatStripT heatStripP 8 false := by decide +kernel
theorem heatStripEdge08True : heatEdgeCheck heatStripT heatStripP 8 true := by decide +kernel
theorem heatStripEdge09False : heatEdgeCheck heatStripT heatStripP 9 false := by decide +kernel
theorem heatStripEdge09True : heatEdgeCheck heatStripT heatStripP 9 true := by decide +kernel
theorem heatStripEdge10False : heatEdgeCheck heatStripT heatStripP 10 false := by decide +kernel
theorem heatStripEdge10True : heatEdgeCheck heatStripT heatStripP 10 true := by decide +kernel
theorem heatStripEdge11False : heatEdgeCheck heatStripT heatStripP 11 false := by decide +kernel
theorem heatStripEdge11True : heatEdgeCheck heatStripT heatStripP 11 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge11True
