import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR002Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR002Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1747058137872681387422636,1756553019056840953356930,true⟩,⟨0,0,true⟩⟩, ⟨(-303836197890941446202122),(-284846435522691033820491),true⟩, ⟨3299160888589230792619901,3359777358720940182269913,true⟩⟩
theorem rightPrimalR002Q00P_ok : rightPrimalR002Q00P.encloses (primalThetaParameters rightPrimalR002Q00T (Grid.ofRats (23/25) (37/40))) := by decide +kernel

def rightPrimalR002Q00U : ℕ → ℚ
  | 0 => (-2523/1000)
  | 1 => (-2177/1000)
  | 2 => (-177/100)
  | 3 => (-1513/1000)
  | 4 => (-1517/1000)
  | 5 => (-447/250)
  | 6 => (-437/200)
  | 7 => (-2489/1000)
  | _ => 0
theorem rightPrimalR002Q00Sample0 : primalSampleCheck rightPrimalR002Q00T rightPrimalR002Q00P 0 (rightPrimalR002Q00U 0)=true := by decide +kernel
theorem rightPrimalR002Q00Sample1 : primalSampleCheck rightPrimalR002Q00T rightPrimalR002Q00P 1 (rightPrimalR002Q00U 1)=true := by decide +kernel
theorem rightPrimalR002Q00Sample2 : primalSampleCheck rightPrimalR002Q00T rightPrimalR002Q00P 2 (rightPrimalR002Q00U 2)=true := by decide +kernel
theorem rightPrimalR002Q00Sample3 : primalSampleCheck rightPrimalR002Q00T rightPrimalR002Q00P 3 (rightPrimalR002Q00U 3)=true := by decide +kernel
theorem rightPrimalR002Q00Sample4 : primalSampleCheck rightPrimalR002Q00T rightPrimalR002Q00P 4 (rightPrimalR002Q00U 4)=true := by decide +kernel
theorem rightPrimalR002Q00Sample5 : primalSampleCheck rightPrimalR002Q00T rightPrimalR002Q00P 5 (rightPrimalR002Q00U 5)=true := by decide +kernel
theorem rightPrimalR002Q00Sample6 : primalSampleCheck rightPrimalR002Q00T rightPrimalR002Q00P 6 (rightPrimalR002Q00U 6)=true := by decide +kernel
theorem rightPrimalR002Q00Sample7 : primalSampleCheck rightPrimalR002Q00T rightPrimalR002Q00P 7 (rightPrimalR002Q00U 7)=true := by decide +kernel

theorem rightPrimalR002Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((23/25):ℝ)≤a) (au : a≤((37/40):ℝ)) : thetaHorizontalPeriod t a≤(((-19252337796145798026842605589/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR002Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR002Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR002Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR002Q00Sample0
    · exact rightPrimalR002Q00Sample1
    · exact rightPrimalR002Q00Sample2
    · exact rightPrimalR002Q00Sample3
    · exact rightPrimalR002Q00Sample4
    · exact rightPrimalR002Q00Sample5
    · exact rightPrimalR002Q00Sample6
    · exact rightPrimalR002Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR002Q00_period_bound
