import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR001Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR001Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1728068375504499694518713,1737563256688659260452946,true⟩,⟨0,0,true⟩⟩, ⟨(-341815722627304832010089),(-322825960259054419628336),true⟩, ⟨3306553747177051132376440,3367319479191032247675660,true⟩⟩
theorem rightPrimalR001Q10P_ok : rightPrimalR001Q10P.encloses (primalThetaParameters rightPrimalR001Q10T (Grid.ofRats (91/100) (183/200))) := by decide +kernel

def rightPrimalR001Q10U : ℕ → ℚ
  | 0 => (-2511/1000)
  | 1 => (-43/20)
  | 2 => (-437/250)
  | 3 => (-151/100)
  | 4 => (-1533/1000)
  | 5 => (-909/500)
  | 6 => (-1107/500)
  | 7 => (-2501/1000)
  | _ => 0
theorem rightPrimalR001Q10Sample0 : primalSampleCheck rightPrimalR001Q10T rightPrimalR001Q10P 0 (rightPrimalR001Q10U 0)=true := by decide +kernel
theorem rightPrimalR001Q10Sample1 : primalSampleCheck rightPrimalR001Q10T rightPrimalR001Q10P 1 (rightPrimalR001Q10U 1)=true := by decide +kernel
theorem rightPrimalR001Q10Sample2 : primalSampleCheck rightPrimalR001Q10T rightPrimalR001Q10P 2 (rightPrimalR001Q10U 2)=true := by decide +kernel
theorem rightPrimalR001Q10Sample3 : primalSampleCheck rightPrimalR001Q10T rightPrimalR001Q10P 3 (rightPrimalR001Q10U 3)=true := by decide +kernel
theorem rightPrimalR001Q10Sample4 : primalSampleCheck rightPrimalR001Q10T rightPrimalR001Q10P 4 (rightPrimalR001Q10U 4)=true := by decide +kernel
theorem rightPrimalR001Q10Sample5 : primalSampleCheck rightPrimalR001Q10T rightPrimalR001Q10P 5 (rightPrimalR001Q10U 5)=true := by decide +kernel
theorem rightPrimalR001Q10Sample6 : primalSampleCheck rightPrimalR001Q10T rightPrimalR001Q10P 6 (rightPrimalR001Q10U 6)=true := by decide +kernel
theorem rightPrimalR001Q10Sample7 : primalSampleCheck rightPrimalR001Q10T rightPrimalR001Q10P 7 (rightPrimalR001Q10U 7)=true := by decide +kernel

theorem rightPrimalR001Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((91/100):ℝ)≤a) (au : a≤((183/200):ℝ)) : thetaHorizontalPeriod t a≤(((-18979693138327219468140223759/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR001Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR001Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR001Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR001Q10Sample0
    · exact rightPrimalR001Q10Sample1
    · exact rightPrimalR001Q10Sample2
    · exact rightPrimalR001Q10Sample3
    · exact rightPrimalR001Q10Sample4
    · exact rightPrimalR001Q10Sample5
    · exact rightPrimalR001Q10Sample6
    · exact rightPrimalR001Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR001Q10_period_bound
