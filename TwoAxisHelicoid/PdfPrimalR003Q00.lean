import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR003Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR003Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1766047900240863080326561,1775542781425022646260914,true⟩,⟨0,0,true⟩⟩, ⟨(-265856673154578060394153),(-246866910786327648012642),true⟩, ⟨3288541514465245504923272,3348835395603035970561833,true⟩⟩
theorem rightPrimalR003Q00P_ok : rightPrimalR003Q00P.encloses (primalThetaParameters rightPrimalR003Q00T (Grid.ofRats (93/100) (187/200))) := by decide +kernel

def rightPrimalR003Q00U : ℕ → ℚ
  | 0 => (-633/250)
  | 1 => (-1103/500)
  | 2 => (-9/5)
  | 3 => (-153/100)
  | 4 => (-1513/1000)
  | 5 => (-1767/1000)
  | 6 => (-2159/1000)
  | 7 => (-1237/500)
  | _ => 0
theorem rightPrimalR003Q00Sample0 : primalSampleCheck rightPrimalR003Q00T rightPrimalR003Q00P 0 (rightPrimalR003Q00U 0)=true := by decide +kernel
theorem rightPrimalR003Q00Sample1 : primalSampleCheck rightPrimalR003Q00T rightPrimalR003Q00P 1 (rightPrimalR003Q00U 1)=true := by decide +kernel
theorem rightPrimalR003Q00Sample2 : primalSampleCheck rightPrimalR003Q00T rightPrimalR003Q00P 2 (rightPrimalR003Q00U 2)=true := by decide +kernel
theorem rightPrimalR003Q00Sample3 : primalSampleCheck rightPrimalR003Q00T rightPrimalR003Q00P 3 (rightPrimalR003Q00U 3)=true := by decide +kernel
theorem rightPrimalR003Q00Sample4 : primalSampleCheck rightPrimalR003Q00T rightPrimalR003Q00P 4 (rightPrimalR003Q00U 4)=true := by decide +kernel
theorem rightPrimalR003Q00Sample5 : primalSampleCheck rightPrimalR003Q00T rightPrimalR003Q00P 5 (rightPrimalR003Q00U 5)=true := by decide +kernel
theorem rightPrimalR003Q00Sample6 : primalSampleCheck rightPrimalR003Q00T rightPrimalR003Q00P 6 (rightPrimalR003Q00U 6)=true := by decide +kernel
theorem rightPrimalR003Q00Sample7 : primalSampleCheck rightPrimalR003Q00T rightPrimalR003Q00P 7 (rightPrimalR003Q00U 7)=true := by decide +kernel

theorem rightPrimalR003Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((93/100):ℝ)≤a) (au : a≤((187/200):ℝ)) : thetaHorizontalPeriod t a≤(((-19388335322621179734218904363/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR003Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR003Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR003Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR003Q00Sample0
    · exact rightPrimalR003Q00Sample1
    · exact rightPrimalR003Q00Sample2
    · exact rightPrimalR003Q00Sample3
    · exact rightPrimalR003Q00Sample4
    · exact rightPrimalR003Q00Sample5
    · exact rightPrimalR003Q00Sample6
    · exact rightPrimalR003Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR003Q00_period_bound
