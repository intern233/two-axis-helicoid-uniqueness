import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR003Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR003Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1766047900240863080326561,1775542781425022646260914,true⟩,⟨0,0,true⟩⟩, ⟨(-265856673154578060394153),(-246866910786327648012642),true⟩, ⟨3283777055924323272472210,3343861115860949350675274,true⟩⟩
theorem rightPrimalR003Q10P_ok : rightPrimalR003Q10P.encloses (primalThetaParameters rightPrimalR003Q10T (Grid.ofRats (93/100) (187/200))) := by decide +kernel

def rightPrimalR003Q10U : ℕ → ℚ
  | 0 => (-253/100)
  | 1 => (-276/125)
  | 2 => (-1809/1000)
  | 3 => (-771/500)
  | 4 => (-61/40)
  | 5 => (-222/125)
  | 6 => (-2161/1000)
  | 7 => (-309/125)
  | _ => 0
theorem rightPrimalR003Q10Sample0 : primalSampleCheck rightPrimalR003Q10T rightPrimalR003Q10P 0 (rightPrimalR003Q10U 0)=true := by decide +kernel
theorem rightPrimalR003Q10Sample1 : primalSampleCheck rightPrimalR003Q10T rightPrimalR003Q10P 1 (rightPrimalR003Q10U 1)=true := by decide +kernel
theorem rightPrimalR003Q10Sample2 : primalSampleCheck rightPrimalR003Q10T rightPrimalR003Q10P 2 (rightPrimalR003Q10U 2)=true := by decide +kernel
theorem rightPrimalR003Q10Sample3 : primalSampleCheck rightPrimalR003Q10T rightPrimalR003Q10P 3 (rightPrimalR003Q10U 3)=true := by decide +kernel
theorem rightPrimalR003Q10Sample4 : primalSampleCheck rightPrimalR003Q10T rightPrimalR003Q10P 4 (rightPrimalR003Q10U 4)=true := by decide +kernel
theorem rightPrimalR003Q10Sample5 : primalSampleCheck rightPrimalR003Q10T rightPrimalR003Q10P 5 (rightPrimalR003Q10U 5)=true := by decide +kernel
theorem rightPrimalR003Q10Sample6 : primalSampleCheck rightPrimalR003Q10T rightPrimalR003Q10P 6 (rightPrimalR003Q10U 6)=true := by decide +kernel
theorem rightPrimalR003Q10Sample7 : primalSampleCheck rightPrimalR003Q10T rightPrimalR003Q10P 7 (rightPrimalR003Q10U 7)=true := by decide +kernel

theorem rightPrimalR003Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((93/100):ℝ)≤a) (au : a≤((187/200):ℝ)) : thetaHorizontalPeriod t a≤(((-19388335322621179734218904363/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR003Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR003Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR003Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR003Q10Sample0
    · exact rightPrimalR003Q10Sample1
    · exact rightPrimalR003Q10Sample2
    · exact rightPrimalR003Q10Sample3
    · exact rightPrimalR003Q10Sample4
    · exact rightPrimalR003Q10Sample5
    · exact rightPrimalR003Q10Sample6
    · exact rightPrimalR003Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR003Q10_period_bound
