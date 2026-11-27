import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge04False : heatEdgeCheck heatStripT heatStripP 4 false := by decide +kernel
theorem heatStripEdge04True : heatEdgeCheck heatStripT heatStripP 4 true := by decide +kernel
theorem heatStripEdge05False : heatEdgeCheck heatStripT heatStripP 5 false := by decide +kernel
theorem heatStripEdge05True : heatEdgeCheck heatStripT heatStripP 5 true := by decide +kernel
theorem heatStripEdge06False : heatEdgeCheck heatStripT heatStripP 6 false := by decide +kernel
theorem heatStripEdge06True : heatEdgeCheck heatStripT heatStripP 6 true := by decide +kernel
theorem heatStripEdge07False : heatEdgeCheck heatStripT heatStripP 7 false := by decide +kernel
theorem heatStripEdge07True : heatEdgeCheck heatStripT heatStripP 7 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge07True
