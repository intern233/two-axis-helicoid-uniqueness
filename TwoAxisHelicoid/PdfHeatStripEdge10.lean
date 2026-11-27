import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge40False : heatEdgeCheck heatStripT heatStripP 40 false := by decide +kernel
theorem heatStripEdge40True : heatEdgeCheck heatStripT heatStripP 40 true := by decide +kernel
theorem heatStripEdge41False : heatEdgeCheck heatStripT heatStripP 41 false := by decide +kernel
theorem heatStripEdge41True : heatEdgeCheck heatStripT heatStripP 41 true := by decide +kernel
theorem heatStripEdge42False : heatEdgeCheck heatStripT heatStripP 42 false := by decide +kernel
theorem heatStripEdge42True : heatEdgeCheck heatStripT heatStripP 42 true := by decide +kernel
theorem heatStripEdge43False : heatEdgeCheck heatStripT heatStripP 43 false := by decide +kernel
theorem heatStripEdge43True : heatEdgeCheck heatStripT heatStripP 43 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge43True
