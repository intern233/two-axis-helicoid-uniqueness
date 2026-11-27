import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR001Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR001Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1728068375504499694518713,1737563256688659260452946,true⟩,⟨0,0,true⟩⟩, ⟨(-341815722627304832010089),(-322825960259054419628336),true⟩, ⟨3311311716097256646424101,3372289328910662929859067,true⟩⟩
theorem rightPrimalR001Q00P_ok : rightPrimalR001Q00P.encloses (primalThetaParameters rightPrimalR001Q00T (Grid.ofRats (91/100) (183/200))) := by decide +kernel

def rightPrimalR001Q00U : ℕ → ℚ
  | 0 => (-2513/1000)
  | 1 => (-2147/1000)
  | 2 => (-1739/1000)
  | 3 => (-749/500)
  | 4 => (-761/500)
  | 5 => (-181/100)
  | 6 => (-553/250)
  | 7 => (-313/125)
  | _ => 0
theorem rightPrimalR001Q00Sample0 : primalSampleCheck rightPrimalR001Q00T rightPrimalR001Q00P 0 (rightPrimalR001Q00U 0)=true := by decide +kernel
theorem rightPrimalR001Q00Sample1 : primalSampleCheck rightPrimalR001Q00T rightPrimalR001Q00P 1 (rightPrimalR001Q00U 1)=true := by decide +kernel
theorem rightPrimalR001Q00Sample2 : primalSampleCheck rightPrimalR001Q00T rightPrimalR001Q00P 2 (rightPrimalR001Q00U 2)=true := by decide +kernel
theorem rightPrimalR001Q00Sample3 : primalSampleCheck rightPrimalR001Q00T rightPrimalR001Q00P 3 (rightPrimalR001Q00U 3)=true := by decide +kernel
theorem rightPrimalR001Q00Sample4 : primalSampleCheck rightPrimalR001Q00T rightPrimalR001Q00P 4 (rightPrimalR001Q00U 4)=true := by decide +kernel
theorem rightPrimalR001Q00Sample5 : primalSampleCheck rightPrimalR001Q00T rightPrimalR001Q00P 5 (rightPrimalR001Q00U 5)=true := by decide +kernel
theorem rightPrimalR001Q00Sample6 : primalSampleCheck rightPrimalR001Q00T rightPrimalR001Q00P 6 (rightPrimalR001Q00U 6)=true := by decide +kernel
theorem rightPrimalR001Q00Sample7 : primalSampleCheck rightPrimalR001Q00T rightPrimalR001Q00P 7 (rightPrimalR001Q00U 7)=true := by decide +kernel

theorem rightPrimalR001Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((91/100):ℝ)≤a) (au : a≤((183/200):ℝ)) : thetaHorizontalPeriod t a≤(((-18979693138327219468140223759/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR001Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR001Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR001Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR001Q00Sample0
    · exact rightPrimalR001Q00Sample1
    · exact rightPrimalR001Q00Sample2
    · exact rightPrimalR001Q00Sample3
    · exact rightPrimalR001Q00Sample4
    · exact rightPrimalR001Q00Sample5
    · exact rightPrimalR001Q00Sample6
    · exact rightPrimalR001Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR001Q00_period_bound
