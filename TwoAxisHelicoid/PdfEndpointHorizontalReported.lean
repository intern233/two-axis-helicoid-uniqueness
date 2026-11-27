import TwoAxisHelicoid.PdfEndpointActual000
import TwoAxisHelicoid.PdfEndpointActual001
import TwoAxisHelicoid.PdfEndpointActual002
import TwoAxisHelicoid.PdfEndpointActual003
import TwoAxisHelicoid.PdfEndpointActual004
import TwoAxisHelicoid.PdfEndpointActual005
import TwoAxisHelicoid.PdfEndpointActual006
import TwoAxisHelicoid.PdfEndpointActual007
import TwoAxisHelicoid.PdfEndpointActual008
import TwoAxisHelicoid.PdfEndpointActual009

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem original_endpoint_ten_horizontal_upper_bounds : ∀ r∈endpointData, ∀ t a : ℝ, (7/5:ℝ)≤t → t≤141/100 → RealMem r.a a → thetaHorizontalPeriod t a≤(r.hUpper:ℝ) := by
  intro r member t a tl tu ha
  simp only [endpointData,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact right_original_horizontal_000 tl tu ha
  · exact right_original_horizontal_001 tl tu ha
  · exact right_original_horizontal_002 tl tu ha
  · exact right_original_horizontal_003 tl tu ha
  · exact right_original_horizontal_004 tl tu ha
  · exact right_original_horizontal_005 tl tu ha
  · exact right_original_horizontal_006 tl tu ha
  · exact right_original_horizontal_007 tl tu ha
  · exact right_original_horizontal_008 tl tu ha
  · exact right_original_horizontal_009 tl tu ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_endpoint_ten_horizontal_upper_bounds
