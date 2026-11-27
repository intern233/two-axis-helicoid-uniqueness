import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR005Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR005Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1804027424977226466134409,1823017187345476878520875,true⟩,⟨0,0,true⟩⟩, ⟨(-189897623681851288778214),(-151918098945419183493023),true⟩, ⟨3238575101172402936811591,3352744934158138320826445,true⟩⟩
theorem rightPrimalR005Q10P_ok : rightPrimalR005Q10P.encloses (primalThetaParameters rightPrimalR005Q10T (Grid.ofRats (19/20) (24/25))) := by decide +kernel

def rightPrimalR005Q10U : ℕ → ℚ
  | 0 => (-2477/1000)
  | 1 => (-2191/1000)
  | 2 => (-447/250)
  | 3 => (-371/250)
  | 4 => (-177/125)
  | 5 => (-809/500)
  | 6 => (-1987/1000)
  | 7 => (-2331/1000)
  | _ => 0
theorem rightPrimalR005Q10Sample0 : primalSampleCheck rightPrimalR005Q10T rightPrimalR005Q10P 0 (rightPrimalR005Q10U 0)=true := by decide +kernel
theorem rightPrimalR005Q10Sample1 : primalSampleCheck rightPrimalR005Q10T rightPrimalR005Q10P 1 (rightPrimalR005Q10U 1)=true := by decide +kernel
theorem rightPrimalR005Q10Sample2 : primalSampleCheck rightPrimalR005Q10T rightPrimalR005Q10P 2 (rightPrimalR005Q10U 2)=true := by decide +kernel
theorem rightPrimalR005Q10Sample3 : primalSampleCheck rightPrimalR005Q10T rightPrimalR005Q10P 3 (rightPrimalR005Q10U 3)=true := by decide +kernel
theorem rightPrimalR005Q10Sample4 : primalSampleCheck rightPrimalR005Q10T rightPrimalR005Q10P 4 (rightPrimalR005Q10U 4)=true := by decide +kernel
theorem rightPrimalR005Q10Sample5 : primalSampleCheck rightPrimalR005Q10T rightPrimalR005Q10P 5 (rightPrimalR005Q10U 5)=true := by decide +kernel
theorem rightPrimalR005Q10Sample6 : primalSampleCheck rightPrimalR005Q10T rightPrimalR005Q10P 6 (rightPrimalR005Q10U 6)=true := by decide +kernel
theorem rightPrimalR005Q10Sample7 : primalSampleCheck rightPrimalR005Q10T rightPrimalR005Q10P 7 (rightPrimalR005Q10U 7)=true := by decide +kernel

theorem rightPrimalR005Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((19/20):ℝ)≤a) (au : a≤((24/25):ℝ)) : thetaHorizontalPeriod t a≤(((-4643737067978148485993478787/2475880078570760549798248448):ℚ):ℝ) := by
  have Tmem : rightPrimalR005Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR005Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR005Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR005Q10Sample0
    · exact rightPrimalR005Q10Sample1
    · exact rightPrimalR005Q10Sample2
    · exact rightPrimalR005Q10Sample3
    · exact rightPrimalR005Q10Sample4
    · exact rightPrimalR005Q10Sample5
    · exact rightPrimalR005Q10Sample6
    · exact rightPrimalR005Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR005Q10_period_bound
