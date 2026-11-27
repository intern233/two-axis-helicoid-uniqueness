import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR009Q01T := Grid.ofRats (7/5) (281/200)
def rightPrimalR009Q01P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1889481355634044084202067,1898976236818203650136812,true⟩,⟨0,0,true⟩⟩, ⟨(-18989762368216052642353),34359738368,true⟩, ⟨3255648277924558562679341,3314740717073200243304275,true⟩⟩
theorem rightPrimalR009Q01P_ok : rightPrimalR009Q01P.encloses (primalThetaParameters rightPrimalR009Q01T (Grid.ofRats (199/200) 1)) := by decide +kernel

def rightPrimalR009Q01U : ℕ → ℚ
  | 0 => (-2571/1000)
  | 1 => (-2393/1000)
  | 2 => (-2021/1000)
  | 3 => (-419/250)
  | 4 => (-307/200)
  | 5 => (-417/250)
  | 6 => (-251/125)
  | 7 => (-1189/500)
  | _ => 0
theorem rightPrimalR009Q01Sample0 : primalSampleCheck rightPrimalR009Q01T rightPrimalR009Q01P 0 (rightPrimalR009Q01U 0)=true := by decide +kernel
theorem rightPrimalR009Q01Sample1 : primalSampleCheck rightPrimalR009Q01T rightPrimalR009Q01P 1 (rightPrimalR009Q01U 1)=true := by decide +kernel
theorem rightPrimalR009Q01Sample2 : primalSampleCheck rightPrimalR009Q01T rightPrimalR009Q01P 2 (rightPrimalR009Q01U 2)=true := by decide +kernel
theorem rightPrimalR009Q01Sample3 : primalSampleCheck rightPrimalR009Q01T rightPrimalR009Q01P 3 (rightPrimalR009Q01U 3)=true := by decide +kernel
theorem rightPrimalR009Q01Sample4 : primalSampleCheck rightPrimalR009Q01T rightPrimalR009Q01P 4 (rightPrimalR009Q01U 4)=true := by decide +kernel
theorem rightPrimalR009Q01Sample5 : primalSampleCheck rightPrimalR009Q01T rightPrimalR009Q01P 5 (rightPrimalR009Q01U 5)=true := by decide +kernel
theorem rightPrimalR009Q01Sample6 : primalSampleCheck rightPrimalR009Q01T rightPrimalR009Q01P 6 (rightPrimalR009Q01U 6)=true := by decide +kernel
theorem rightPrimalR009Q01Sample7 : primalSampleCheck rightPrimalR009Q01T rightPrimalR009Q01P 7 (rightPrimalR009Q01U 7)=true := by decide +kernel

theorem rightPrimalR009Q01_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((199/200):ℝ)≤a) (au : a≤(1:ℝ)) : thetaHorizontalPeriod t a≤(((-9705314663351274067227357767/4951760157141521099596496896):ℚ):ℝ) := by
  have Tmem : rightPrimalR009Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR009Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR009Q01U
  · intro k
    fin_cases k
    · exact rightPrimalR009Q01Sample0
    · exact rightPrimalR009Q01Sample1
    · exact rightPrimalR009Q01Sample2
    · exact rightPrimalR009Q01Sample3
    · exact rightPrimalR009Q01Sample4
    · exact rightPrimalR009Q01Sample5
    · exact rightPrimalR009Q01Sample6
    · exact rightPrimalR009Q01Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR009Q01_period_bound
