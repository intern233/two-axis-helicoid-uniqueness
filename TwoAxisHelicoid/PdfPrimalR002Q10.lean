import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR002Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR002Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1747058137872681387422636,1756553019056840953356930,true⟩,⟨0,0,true⟩⟩, ⟨(-303836197890941446202122),(-284846435522691033820491),true⟩, ⟨3294399501840953334425710,3354805122442904912318288,true⟩⟩
theorem rightPrimalR002Q10P_ok : rightPrimalR002Q10P.encloses (primalThetaParameters rightPrimalR002Q10T (Grid.ofRats (23/25) (37/40))) := by decide +kernel

def rightPrimalR002Q10U : ℕ → ℚ
  | 0 => (-2521/1000)
  | 1 => (-2179/1000)
  | 2 => (-889/500)
  | 3 => (-61/40)
  | 4 => (-191/125)
  | 5 => (-449/250)
  | 6 => (-2187/1000)
  | 7 => (-2487/1000)
  | _ => 0
theorem rightPrimalR002Q10Sample0 : primalSampleCheck rightPrimalR002Q10T rightPrimalR002Q10P 0 (rightPrimalR002Q10U 0)=true := by decide +kernel
theorem rightPrimalR002Q10Sample1 : primalSampleCheck rightPrimalR002Q10T rightPrimalR002Q10P 1 (rightPrimalR002Q10U 1)=true := by decide +kernel
theorem rightPrimalR002Q10Sample2 : primalSampleCheck rightPrimalR002Q10T rightPrimalR002Q10P 2 (rightPrimalR002Q10U 2)=true := by decide +kernel
theorem rightPrimalR002Q10Sample3 : primalSampleCheck rightPrimalR002Q10T rightPrimalR002Q10P 3 (rightPrimalR002Q10U 3)=true := by decide +kernel
theorem rightPrimalR002Q10Sample4 : primalSampleCheck rightPrimalR002Q10T rightPrimalR002Q10P 4 (rightPrimalR002Q10U 4)=true := by decide +kernel
theorem rightPrimalR002Q10Sample5 : primalSampleCheck rightPrimalR002Q10T rightPrimalR002Q10P 5 (rightPrimalR002Q10U 5)=true := by decide +kernel
theorem rightPrimalR002Q10Sample6 : primalSampleCheck rightPrimalR002Q10T rightPrimalR002Q10P 6 (rightPrimalR002Q10U 6)=true := by decide +kernel
theorem rightPrimalR002Q10Sample7 : primalSampleCheck rightPrimalR002Q10T rightPrimalR002Q10P 7 (rightPrimalR002Q10U 7)=true := by decide +kernel

theorem rightPrimalR002Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((23/25):ℝ)≤a) (au : a≤((37/40):ℝ)) : thetaHorizontalPeriod t a≤(((-19252337796145798026842605589/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR002Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR002Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR002Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR002Q10Sample0
    · exact rightPrimalR002Q10Sample1
    · exact rightPrimalR002Q10Sample2
    · exact rightPrimalR002Q10Sample3
    · exact rightPrimalR002Q10Sample4
    · exact rightPrimalR002Q10Sample5
    · exact rightPrimalR002Q10Sample6
    · exact rightPrimalR002Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR002Q10_period_bound
