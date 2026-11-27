import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR006Q10T := Grid.ofRats (281/200) (141/100)
def rightPrimalR006Q10P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1823017187345408159038332,1832512068529567724972867,true⟩,⟨0,0,true⟩⟩, ⟨(-151918098945487902970247),(-132928336577237490589099),true⟩, ⟨3260900500501662766472055,3320243860129756674928996,true⟩⟩
theorem rightPrimalR006Q10P_ok : rightPrimalR006Q10P.encloses (primalThetaParameters rightPrimalR006Q10T (Grid.ofRats (24/25) (193/200))) := by decide +kernel

def rightPrimalR006Q10U : ℕ → ℚ
  | 0 => (-2551/1000)
  | 1 => (-459/200)
  | 2 => (-381/200)
  | 3 => (-1601/1000)
  | 4 => (-763/500)
  | 5 => (-431/250)
  | 6 => (-261/125)
  | 7 => (-607/250)
  | _ => 0
theorem rightPrimalR006Q10Sample0 : primalSampleCheck rightPrimalR006Q10T rightPrimalR006Q10P 0 (rightPrimalR006Q10U 0)=true := by decide +kernel
theorem rightPrimalR006Q10Sample1 : primalSampleCheck rightPrimalR006Q10T rightPrimalR006Q10P 1 (rightPrimalR006Q10U 1)=true := by decide +kernel
theorem rightPrimalR006Q10Sample2 : primalSampleCheck rightPrimalR006Q10T rightPrimalR006Q10P 2 (rightPrimalR006Q10U 2)=true := by decide +kernel
theorem rightPrimalR006Q10Sample3 : primalSampleCheck rightPrimalR006Q10T rightPrimalR006Q10P 3 (rightPrimalR006Q10U 3)=true := by decide +kernel
theorem rightPrimalR006Q10Sample4 : primalSampleCheck rightPrimalR006Q10T rightPrimalR006Q10P 4 (rightPrimalR006Q10U 4)=true := by decide +kernel
theorem rightPrimalR006Q10Sample5 : primalSampleCheck rightPrimalR006Q10T rightPrimalR006Q10P 5 (rightPrimalR006Q10U 5)=true := by decide +kernel
theorem rightPrimalR006Q10Sample6 : primalSampleCheck rightPrimalR006Q10T rightPrimalR006Q10P 6 (rightPrimalR006Q10U 6)=true := by decide +kernel
theorem rightPrimalR006Q10Sample7 : primalSampleCheck rightPrimalR006Q10T rightPrimalR006Q10P 7 (rightPrimalR006Q10U 7)=true := by decide +kernel

theorem rightPrimalR006Q10_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((24/25):ℝ)≤a) (au : a≤((193/200):ℝ)) : thetaHorizontalPeriod t a≤(((-19042016524540244183430618433/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR006Q10T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR006Q10P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR006Q10U
  · intro k
    fin_cases k
    · exact rightPrimalR006Q10Sample0
    · exact rightPrimalR006Q10Sample1
    · exact rightPrimalR006Q10Sample2
    · exact rightPrimalR006Q10Sample3
    · exact rightPrimalR006Q10Sample4
    · exact rightPrimalR006Q10Sample5
    · exact rightPrimalR006Q10Sample6
    · exact rightPrimalR006Q10Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR006Q10_period_bound
