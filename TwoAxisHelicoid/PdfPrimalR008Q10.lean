import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR008Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR008Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1860996712081771544846181,1879986474450021957232829,true⟩,⟨0,0,true⟩⟩, ⟨(-75959049472761131354308),(-37979524736329026069477),true⟩, ⟨3225862393828240136241720,3339036921880336825801260,true⟩⟩
theorem rightPrimalR008Q10P_ok : rightPrimalR008Q10P.encloses (primalThetaParameters rightPrimalR008Q10T (Grid.ofRats (49/50) (99/100))) := by decide +kernel

def rightPrimalR008Q10U : ℕ → ℚ
  | 0 => (-2499/1000)
  | 1 => (-57/25)
  | 2 => (-1893/1000)
  | 3 => (-779/500)
  | 4 => (-717/500)
  | 5 => (-1583/1000)
  | 6 => (-1927/1000)
  | 7 => (-1147/500)
  | _ => 0
theorem rightPrimalR008Q10Sample0 : primalSampleCheck rightPrimalR008Q10T rightPrimalR008Q10P 0 (rightPrimalR008Q10U 0)=true := by decide +kernel
theorem rightPrimalR008Q10Sample1 : primalSampleCheck rightPrimalR008Q10T rightPrimalR008Q10P 1 (rightPrimalR008Q10U 1)=true := by decide +kernel
theorem rightPrimalR008Q10Sample2 : primalSampleCheck rightPrimalR008Q10T rightPrimalR008Q10P 2 (rightPrimalR008Q10U 2)=true := by decide +kernel
theorem rightPrimalR008Q10Sample3 : primalSampleCheck rightPrimalR008Q10T rightPrimalR008Q10P 3 (rightPrimalR008Q10U 3)=true := by decide +kernel
theorem rightPrimalR008Q10Sample4 : primalSampleCheck rightPrimalR008Q10T rightPrimalR008Q10P 4 (rightPrimalR008Q10U 4)=true := by decide +kernel
theorem rightPrimalR008Q10Sample5 : primalSampleCheck rightPrimalR008Q10T rightPrimalR008Q10P 5 (rightPrimalR008Q10U 5)=true := by decide +kernel
theorem rightPrimalR008Q10Sample6 : primalSampleCheck rightPrimalR008Q10T rightPrimalR008Q10P 6 (rightPrimalR008Q10U 6)=true := by decide +kernel
theorem rightPrimalR008Q10Sample7 : primalSampleCheck rightPrimalR008Q10T rightPrimalR008Q10P 7 (rightPrimalR008Q10U 7)=true := by decide +kernel

theorem rightPrimalR008Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((49/50):ℝ)≤a) (au : a≤((99/100):ℝ)) : thetaHorizontalPeriod t a≤(((-19027439639081163980098842865/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR008Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR008Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR008Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR008Q10Sample0
    · exact rightPrimalR008Q10Sample1
    · exact rightPrimalR008Q10Sample2
    · exact rightPrimalR008Q10Sample3
    · exact rightPrimalR008Q10Sample4
    · exact rightPrimalR008Q10Sample5
    · exact rightPrimalR008Q10Sample6
    · exact rightPrimalR008Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR008Q10_period_bound
