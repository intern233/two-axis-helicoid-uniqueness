import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR007Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR007Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1842006949713589851942256,1860996712081840264328844,true⟩,⟨0,0,true⟩⟩, ⟨(-113938574209124517162277),(-75959049472692411877326),true⟩, ⟨3228661794849858377914434,3342096315120929758168529,true⟩⟩
theorem rightPrimalR007Q10P_ok : rightPrimalR007Q10P.encloses (primalThetaParameters rightPrimalR007Q10T (Grid.ofRats (97/100) (49/50))) := by decide +kernel

def rightPrimalR007Q10U : ℕ → ℚ
  | 0 => (-2493/1000)
  | 1 => (-2251/1000)
  | 2 => (-1857/1000)
  | 3 => (-383/250)
  | 4 => (-1427/1000)
  | 5 => (-1593/1000)
  | 6 => (-973/500)
  | 7 => (-1153/500)
  | _ => 0
theorem rightPrimalR007Q10Sample0 : primalSampleCheck rightPrimalR007Q10T rightPrimalR007Q10P 0 (rightPrimalR007Q10U 0)=true := by decide +kernel
theorem rightPrimalR007Q10Sample1 : primalSampleCheck rightPrimalR007Q10T rightPrimalR007Q10P 1 (rightPrimalR007Q10U 1)=true := by decide +kernel
theorem rightPrimalR007Q10Sample2 : primalSampleCheck rightPrimalR007Q10T rightPrimalR007Q10P 2 (rightPrimalR007Q10U 2)=true := by decide +kernel
theorem rightPrimalR007Q10Sample3 : primalSampleCheck rightPrimalR007Q10T rightPrimalR007Q10P 3 (rightPrimalR007Q10U 3)=true := by decide +kernel
theorem rightPrimalR007Q10Sample4 : primalSampleCheck rightPrimalR007Q10T rightPrimalR007Q10P 4 (rightPrimalR007Q10U 4)=true := by decide +kernel
theorem rightPrimalR007Q10Sample5 : primalSampleCheck rightPrimalR007Q10T rightPrimalR007Q10P 5 (rightPrimalR007Q10U 5)=true := by decide +kernel
theorem rightPrimalR007Q10Sample6 : primalSampleCheck rightPrimalR007Q10T rightPrimalR007Q10P 6 (rightPrimalR007Q10U 6)=true := by decide +kernel
theorem rightPrimalR007Q10Sample7 : primalSampleCheck rightPrimalR007Q10T rightPrimalR007Q10P 7 (rightPrimalR007Q10U 7)=true := by decide +kernel

theorem rightPrimalR007Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((97/100):ℝ)≤a) (au : a≤((49/50):ℝ)) : thetaHorizontalPeriod t a≤(((-37698701175115388651451622505/19807040628566084398385987584):ℚ):ℝ) := by
  have Tmem : rightPrimalR007Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR007Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR007Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR007Q10Sample0
    · exact rightPrimalR007Q10Sample1
    · exact rightPrimalR007Q10Sample2
    · exact rightPrimalR007Q10Sample3
    · exact rightPrimalR007Q10Sample4
    · exact rightPrimalR007Q10Sample5
    · exact rightPrimalR007Q10Sample6
    · exact rightPrimalR007Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR007Q10_period_bound
