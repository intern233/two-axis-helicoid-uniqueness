import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge48False : heatEdgeCheck heatStripT heatStripP 48 false := by decide +kernel
theorem heatStripEdge48True : heatEdgeCheck heatStripT heatStripP 48 true := by decide +kernel
theorem heatStripEdge49False : heatEdgeCheck heatStripT heatStripP 49 false := by decide +kernel
theorem heatStripEdge49True : heatEdgeCheck heatStripT heatStripP 49 true := by decide +kernel
theorem heatStripEdge50False : heatEdgeCheck heatStripT heatStripP 50 false := by decide +kernel
theorem heatStripEdge50True : heatEdgeCheck heatStripT heatStripP 50 true := by decide +kernel
theorem heatStripEdge51False : heatEdgeCheck heatStripT heatStripP 51 false := by decide +kernel
theorem heatStripEdge51True : heatEdgeCheck heatStripT heatStripP 51 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge51True
