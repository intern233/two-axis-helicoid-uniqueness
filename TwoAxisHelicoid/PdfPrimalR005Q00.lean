import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR005Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR005Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1804027424977226466134409,1823017187345476878520875,true⟩,⟨0,0,true⟩⟩, ⟨(-189897623681851288778214),(-151918098945419183493023),true⟩, ⟨3243284617097399870143913,3357787371954216828002119,true⟩⟩
theorem rightPrimalR005Q00P_ok : rightPrimalR005Q00P.encloses (primalThetaParameters rightPrimalR005Q00T (Grid.ofRats (19/20) (24/25))) := by decide +kernel

def rightPrimalR005Q00U : ℕ → ℚ
  | 0 => (-62/25)
  | 1 => (-2189/1000)
  | 2 => (-89/50)
  | 3 => (-1473/1000)
  | 4 => (-351/250)
  | 5 => (-1609/1000)
  | 6 => (-1983/1000)
  | 7 => (-583/250)
  | _ => 0
theorem rightPrimalR005Q00Sample0 : primalSampleCheck rightPrimalR005Q00T rightPrimalR005Q00P 0 (rightPrimalR005Q00U 0)=true := by decide +kernel
theorem rightPrimalR005Q00Sample1 : primalSampleCheck rightPrimalR005Q00T rightPrimalR005Q00P 1 (rightPrimalR005Q00U 1)=true := by decide +kernel
theorem rightPrimalR005Q00Sample2 : primalSampleCheck rightPrimalR005Q00T rightPrimalR005Q00P 2 (rightPrimalR005Q00U 2)=true := by decide +kernel
theorem rightPrimalR005Q00Sample3 : primalSampleCheck rightPrimalR005Q00T rightPrimalR005Q00P 3 (rightPrimalR005Q00U 3)=true := by decide +kernel
theorem rightPrimalR005Q00Sample4 : primalSampleCheck rightPrimalR005Q00T rightPrimalR005Q00P 4 (rightPrimalR005Q00U 4)=true := by decide +kernel
theorem rightPrimalR005Q00Sample5 : primalSampleCheck rightPrimalR005Q00T rightPrimalR005Q00P 5 (rightPrimalR005Q00U 5)=true := by decide +kernel
theorem rightPrimalR005Q00Sample6 : primalSampleCheck rightPrimalR005Q00T rightPrimalR005Q00P 6 (rightPrimalR005Q00U 6)=true := by decide +kernel
theorem rightPrimalR005Q00Sample7 : primalSampleCheck rightPrimalR005Q00T rightPrimalR005Q00P 7 (rightPrimalR005Q00U 7)=true := by decide +kernel

theorem rightPrimalR005Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((19/20):ℝ)≤a) (au : a≤((24/25):ℝ)) : thetaHorizontalPeriod t a≤(((-4643737067978148485993478787/2475880078570760549798248448):ℚ):ℝ) := by
  have Tmem : rightPrimalR005Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR005Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR005Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR005Q00Sample0
    · exact rightPrimalR005Q00Sample1
    · exact rightPrimalR005Q00Sample2
    · exact rightPrimalR005Q00Sample3
    · exact rightPrimalR005Q00Sample4
    · exact rightPrimalR005Q00Sample5
    · exact rightPrimalR005Q00Sample6
    · exact rightPrimalR005Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR005Q00_period_bound
