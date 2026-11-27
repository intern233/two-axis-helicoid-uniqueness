import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR004Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR004Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1785037662609044773230485,1804027424977295185616892,true⟩,⟨0,0,true⟩⟩, ⟨(-227877148418214674586183),(-189897623681782569300869),true⟩, ⟨3245708857734252448854536,3360355597613496358210708,true⟩⟩
theorem rightPrimalR004Q10P_ok : rightPrimalR004Q10P.encloses (primalThetaParameters rightPrimalR004Q10T (Grid.ofRats (47/50) (19/20))) := by decide +kernel

def rightPrimalR004Q10U : ℕ → ℚ
  | 0 => (-617/250)
  | 1 => (-54/25)
  | 2 => (-877/500)
  | 3 => (-1463/1000)
  | 4 => (-707/500)
  | 5 => (-1633/1000)
  | 6 => (-2009/1000)
  | 7 => (-2343/1000)
  | _ => 0
theorem rightPrimalR004Q10Sample0 : primalSampleCheck rightPrimalR004Q10T rightPrimalR004Q10P 0 (rightPrimalR004Q10U 0)=true := by decide +kernel
theorem rightPrimalR004Q10Sample1 : primalSampleCheck rightPrimalR004Q10T rightPrimalR004Q10P 1 (rightPrimalR004Q10U 1)=true := by decide +kernel
theorem rightPrimalR004Q10Sample2 : primalSampleCheck rightPrimalR004Q10T rightPrimalR004Q10P 2 (rightPrimalR004Q10U 2)=true := by decide +kernel
theorem rightPrimalR004Q10Sample3 : primalSampleCheck rightPrimalR004Q10T rightPrimalR004Q10P 3 (rightPrimalR004Q10U 3)=true := by decide +kernel
theorem rightPrimalR004Q10Sample4 : primalSampleCheck rightPrimalR004Q10T rightPrimalR004Q10P 4 (rightPrimalR004Q10U 4)=true := by decide +kernel
theorem rightPrimalR004Q10Sample5 : primalSampleCheck rightPrimalR004Q10T rightPrimalR004Q10P 5 (rightPrimalR004Q10U 5)=true := by decide +kernel
theorem rightPrimalR004Q10Sample6 : primalSampleCheck rightPrimalR004Q10T rightPrimalR004Q10P 6 (rightPrimalR004Q10U 6)=true := by decide +kernel
theorem rightPrimalR004Q10Sample7 : primalSampleCheck rightPrimalR004Q10T rightPrimalR004Q10P 7 (rightPrimalR004Q10U 7)=true := by decide +kernel

theorem rightPrimalR004Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((47/50):ℝ)≤a) (au : a≤((19/20):ℝ)) : thetaHorizontalPeriod t a≤(((-37233978647365851779223361019/19807040628566084398385987584):ℚ):ℝ) := by
  have Tmem : rightPrimalR004Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR004Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR004Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR004Q10Sample0
    · exact rightPrimalR004Q10Sample1
    · exact rightPrimalR004Q10Sample2
    · exact rightPrimalR004Q10Sample3
    · exact rightPrimalR004Q10Sample4
    · exact rightPrimalR004Q10Sample5
    · exact rightPrimalR004Q10Sample6
    · exact rightPrimalR004Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR004Q10_period_bound
