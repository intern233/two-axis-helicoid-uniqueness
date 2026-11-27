import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR009Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR009Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1879986474449953237750105,1889481355634112803684822,true⟩,⟨0,0,true⟩⟩, ⟨(-37979524736397745546338),(-18989762368147333165553),true⟩, ⟨3251218919663392269553124,3310146552926999651495421,true⟩⟩
theorem rightPrimalR009Q10P_ok : rightPrimalR009Q10P.encloses (primalThetaParameters rightPrimalR009Q10T (Grid.ofRats (99/100) (199/200))) := by decide +kernel

def rightPrimalR009Q10U : ℕ → ℚ
  | 0 => (-1283/500)
  | 1 => (-2379/1000)
  | 2 => (-251/125)
  | 3 => (-1673/1000)
  | 4 => (-1543/1000)
  | 5 => (-421/250)
  | 6 => (-2023/1000)
  | 7 => (-298/125)
  | _ => 0
theorem rightPrimalR009Q10Sample0 : primalSampleCheck rightPrimalR009Q10T rightPrimalR009Q10P 0 (rightPrimalR009Q10U 0)=true := by decide +kernel
theorem rightPrimalR009Q10Sample1 : primalSampleCheck rightPrimalR009Q10T rightPrimalR009Q10P 1 (rightPrimalR009Q10U 1)=true := by decide +kernel
theorem rightPrimalR009Q10Sample2 : primalSampleCheck rightPrimalR009Q10T rightPrimalR009Q10P 2 (rightPrimalR009Q10U 2)=true := by decide +kernel
theorem rightPrimalR009Q10Sample3 : primalSampleCheck rightPrimalR009Q10T rightPrimalR009Q10P 3 (rightPrimalR009Q10U 3)=true := by decide +kernel
theorem rightPrimalR009Q10Sample4 : primalSampleCheck rightPrimalR009Q10T rightPrimalR009Q10P 4 (rightPrimalR009Q10U 4)=true := by decide +kernel
theorem rightPrimalR009Q10Sample5 : primalSampleCheck rightPrimalR009Q10T rightPrimalR009Q10P 5 (rightPrimalR009Q10U 5)=true := by decide +kernel
theorem rightPrimalR009Q10Sample6 : primalSampleCheck rightPrimalR009Q10T rightPrimalR009Q10P 6 (rightPrimalR009Q10U 6)=true := by decide +kernel
theorem rightPrimalR009Q10Sample7 : primalSampleCheck rightPrimalR009Q10T rightPrimalR009Q10P 7 (rightPrimalR009Q10U 7)=true := by decide +kernel

theorem rightPrimalR009Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((99/100):ℝ)≤a) (au : a≤((199/200):ℝ)) : thetaHorizontalPeriod t a≤(((-9705314663351274067227357767/4951760157141521099596496896):ℚ):ℝ) := by
  have Tmem : rightPrimalR009Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR009Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR009Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR009Q10Sample0
    · exact rightPrimalR009Q10Sample1
    · exact rightPrimalR009Q10Sample2
    · exact rightPrimalR009Q10Sample3
    · exact rightPrimalR009Q10Sample4
    · exact rightPrimalR009Q10Sample5
    · exact rightPrimalR009Q10Sample6
    · exact rightPrimalR009Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR009Q10_period_bound
