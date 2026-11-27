import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR008Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR008Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1860996712081771544846181,1879986474450021957232829,true⟩,⟨0,0,true⟩⟩, ⟨(-75959049472761131354308),(-37979524736329026069477),true⟩, ⟨3230578159051146780913009,3344079334385509742299370,true⟩⟩
theorem rightPrimalR008Q00P_ok : rightPrimalR008Q00P.encloses (primalThetaParameters rightPrimalR008Q00T (Grid.ofRats (49/50) (99/100))) := by decide +kernel

def rightPrimalR008Q00U : ℕ → ℚ
  | 0 => (-2503/1000)
  | 1 => (-57/25)
  | 2 => (-1887/1000)
  | 3 => (-1547/1000)
  | 4 => (-711/500)
  | 5 => (-393/250)
  | 6 => (-961/500)
  | 7 => (-1147/500)
  | _ => 0
theorem rightPrimalR008Q00Sample0 : primalSampleCheck rightPrimalR008Q00T rightPrimalR008Q00P 0 (rightPrimalR008Q00U 0)=true := by decide +kernel
theorem rightPrimalR008Q00Sample1 : primalSampleCheck rightPrimalR008Q00T rightPrimalR008Q00P 1 (rightPrimalR008Q00U 1)=true := by decide +kernel
theorem rightPrimalR008Q00Sample2 : primalSampleCheck rightPrimalR008Q00T rightPrimalR008Q00P 2 (rightPrimalR008Q00U 2)=true := by decide +kernel
theorem rightPrimalR008Q00Sample3 : primalSampleCheck rightPrimalR008Q00T rightPrimalR008Q00P 3 (rightPrimalR008Q00U 3)=true := by decide +kernel
theorem rightPrimalR008Q00Sample4 : primalSampleCheck rightPrimalR008Q00T rightPrimalR008Q00P 4 (rightPrimalR008Q00U 4)=true := by decide +kernel
theorem rightPrimalR008Q00Sample5 : primalSampleCheck rightPrimalR008Q00T rightPrimalR008Q00P 5 (rightPrimalR008Q00U 5)=true := by decide +kernel
theorem rightPrimalR008Q00Sample6 : primalSampleCheck rightPrimalR008Q00T rightPrimalR008Q00P 6 (rightPrimalR008Q00U 6)=true := by decide +kernel
theorem rightPrimalR008Q00Sample7 : primalSampleCheck rightPrimalR008Q00T rightPrimalR008Q00P 7 (rightPrimalR008Q00U 7)=true := by decide +kernel

theorem rightPrimalR008Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((49/50):ℝ)≤a) (au : a≤((99/100):ℝ)) : thetaHorizontalPeriod t a≤(((-19027439639081163980098842865/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR008Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR008Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR008Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR008Q00Sample0
    · exact rightPrimalR008Q00Sample1
    · exact rightPrimalR008Q00Sample2
    · exact rightPrimalR008Q00Sample3
    · exact rightPrimalR008Q00Sample4
    · exact rightPrimalR008Q00Sample5
    · exact rightPrimalR008Q00Sample6
    · exact rightPrimalR008Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR008Q00_period_bound
