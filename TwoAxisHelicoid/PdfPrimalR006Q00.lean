import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR006Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR006Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1823017187345408159038332,1832512068529567724972867,true⟩,⟨0,0,true⟩⟩, ⟨(-151918098945487902970247),(-132928336577237490589099),true⟩, ⟨3265672072934983406687713,3325222175719552500199136,true⟩⟩
theorem rightPrimalR006Q00P_ok : rightPrimalR006Q00P.encloses (primalThetaParameters rightPrimalR006Q00T (Grid.ofRats (24/25) (193/200))) := by decide +kernel

def rightPrimalR006Q00U : ℕ → ℚ
  | 0 => (-511/200)
  | 1 => (-1147/500)
  | 2 => (-949/500)
  | 3 => (-159/100)
  | 4 => (-757/500)
  | 5 => (-857/500)
  | 6 => (-417/200)
  | 7 => (-243/100)
  | _ => 0
theorem rightPrimalR006Q00Sample0 : primalSampleCheck rightPrimalR006Q00T rightPrimalR006Q00P 0 (rightPrimalR006Q00U 0)=true := by decide +kernel
theorem rightPrimalR006Q00Sample1 : primalSampleCheck rightPrimalR006Q00T rightPrimalR006Q00P 1 (rightPrimalR006Q00U 1)=true := by decide +kernel
theorem rightPrimalR006Q00Sample2 : primalSampleCheck rightPrimalR006Q00T rightPrimalR006Q00P 2 (rightPrimalR006Q00U 2)=true := by decide +kernel
theorem rightPrimalR006Q00Sample3 : primalSampleCheck rightPrimalR006Q00T rightPrimalR006Q00P 3 (rightPrimalR006Q00U 3)=true := by decide +kernel
theorem rightPrimalR006Q00Sample4 : primalSampleCheck rightPrimalR006Q00T rightPrimalR006Q00P 4 (rightPrimalR006Q00U 4)=true := by decide +kernel
theorem rightPrimalR006Q00Sample5 : primalSampleCheck rightPrimalR006Q00T rightPrimalR006Q00P 5 (rightPrimalR006Q00U 5)=true := by decide +kernel
theorem rightPrimalR006Q00Sample6 : primalSampleCheck rightPrimalR006Q00T rightPrimalR006Q00P 6 (rightPrimalR006Q00U 6)=true := by decide +kernel
theorem rightPrimalR006Q00Sample7 : primalSampleCheck rightPrimalR006Q00T rightPrimalR006Q00P 7 (rightPrimalR006Q00U 7)=true := by decide +kernel

theorem rightPrimalR006Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((24/25):ℝ)≤a) (au : a≤((193/200):ℝ)) : thetaHorizontalPeriod t a≤(((-19042016524540244183430618433/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR006Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR006Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR006Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR006Q00Sample0
    · exact rightPrimalR006Q00Sample1
    · exact rightPrimalR006Q00Sample2
    · exact rightPrimalR006Q00Sample3
    · exact rightPrimalR006Q00Sample4
    · exact rightPrimalR006Q00Sample5
    · exact rightPrimalR006Q00Sample6
    · exact rightPrimalR006Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR006Q00_period_bound
