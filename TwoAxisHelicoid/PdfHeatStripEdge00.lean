import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge00False : heatEdgeCheck heatStripT heatStripP 0 false := by decide +kernel
theorem heatStripEdge00True : heatEdgeCheck heatStripT heatStripP 0 true := by decide +kernel
theorem heatStripEdge01False : heatEdgeCheck heatStripT heatStripP 1 false := by decide +kernel
theorem heatStripEdge01True : heatEdgeCheck heatStripT heatStripP 1 true := by decide +kernel
theorem heatStripEdge02False : heatEdgeCheck heatStripT heatStripP 2 false := by decide +kernel
theorem heatStripEdge02True : heatEdgeCheck heatStripT heatStripP 2 true := by decide +kernel
theorem heatStripEdge03False : heatEdgeCheck heatStripT heatStripP 3 false := by decide +kernel
theorem heatStripEdge03True : heatEdgeCheck heatStripT heatStripP 3 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge03True
