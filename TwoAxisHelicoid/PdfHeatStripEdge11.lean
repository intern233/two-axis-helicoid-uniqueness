import TwoAxisHelicoid.PdfHeatStripParameters
import TwoAxisHelicoid.PdfHeatGridSampling
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem heatStripEdge44False : heatEdgeCheck heatStripT heatStripP 44 false := by decide +kernel
theorem heatStripEdge44True : heatEdgeCheck heatStripT heatStripP 44 true := by decide +kernel
theorem heatStripEdge45False : heatEdgeCheck heatStripT heatStripP 45 false := by decide +kernel
theorem heatStripEdge45True : heatEdgeCheck heatStripT heatStripP 45 true := by decide +kernel
theorem heatStripEdge46False : heatEdgeCheck heatStripT heatStripP 46 false := by decide +kernel
theorem heatStripEdge46True : heatEdgeCheck heatStripT heatStripP 46 true := by decide +kernel
theorem heatStripEdge47False : heatEdgeCheck heatStripT heatStripP 47 false := by decide +kernel
theorem heatStripEdge47True : heatEdgeCheck heatStripT heatStripP 47 true := by decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.heatStripEdge47True
