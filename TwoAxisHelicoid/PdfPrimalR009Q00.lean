import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR009Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR009Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1879986474449953237750105,1889481355634112803684822,true⟩,⟨0,0,true⟩⟩, ⟨(-37979524736397745546338),(-18989762368147333165553),true⟩, ⟨3255994418540574330581184,3315125706499055294786159,true⟩⟩
theorem rightPrimalR009Q00P_ok : rightPrimalR009Q00P.encloses (primalThetaParameters rightPrimalR009Q00T (Grid.ofRats (99/100) (199/200))) := by decide +kernel

def rightPrimalR009Q00U : ℕ → ℚ
  | 0 => (-257/100)
  | 1 => (-2379/1000)
  | 2 => (-2003/1000)
  | 3 => (-1663/1000)
  | 4 => (-1531/1000)
  | 5 => (-837/500)
  | 6 => (-1009/500)
  | 7 => (-477/200)
  | _ => 0
theorem rightPrimalR009Q00Sample0 : primalSampleCheck rightPrimalR009Q00T rightPrimalR009Q00P 0 (rightPrimalR009Q00U 0)=true := by decide +kernel
theorem rightPrimalR009Q00Sample1 : primalSampleCheck rightPrimalR009Q00T rightPrimalR009Q00P 1 (rightPrimalR009Q00U 1)=true := by decide +kernel
theorem rightPrimalR009Q00Sample2 : primalSampleCheck rightPrimalR009Q00T rightPrimalR009Q00P 2 (rightPrimalR009Q00U 2)=true := by decide +kernel
theorem rightPrimalR009Q00Sample3 : primalSampleCheck rightPrimalR009Q00T rightPrimalR009Q00P 3 (rightPrimalR009Q00U 3)=true := by decide +kernel
theorem rightPrimalR009Q00Sample4 : primalSampleCheck rightPrimalR009Q00T rightPrimalR009Q00P 4 (rightPrimalR009Q00U 4)=true := by decide +kernel
theorem rightPrimalR009Q00Sample5 : primalSampleCheck rightPrimalR009Q00T rightPrimalR009Q00P 5 (rightPrimalR009Q00U 5)=true := by decide +kernel
theorem rightPrimalR009Q00Sample6 : primalSampleCheck rightPrimalR009Q00T rightPrimalR009Q00P 6 (rightPrimalR009Q00U 6)=true := by decide +kernel
theorem rightPrimalR009Q00Sample7 : primalSampleCheck rightPrimalR009Q00T rightPrimalR009Q00P 7 (rightPrimalR009Q00U 7)=true := by decide +kernel

theorem rightPrimalR009Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((99/100):ℝ)≤a) (au : a≤((199/200):ℝ)) : thetaHorizontalPeriod t a≤(((-9705314663351274067227357767/4951760157141521099596496896):ℚ):ℝ) := by
  have Tmem : rightPrimalR009Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR009Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR009Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR009Q00Sample0
    · exact rightPrimalR009Q00Sample1
    · exact rightPrimalR009Q00Sample2
    · exact rightPrimalR009Q00Sample3
    · exact rightPrimalR009Q00Sample4
    · exact rightPrimalR009Q00Sample5
    · exact rightPrimalR009Q00Sample6
    · exact rightPrimalR009Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR009Q00_period_bound
