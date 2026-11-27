import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR007Q00T := Grid.ofRats (7/5) (281/200)
def rightPrimalR007Q00P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1842006949713589851942256,1860996712081840264328844,true⟩,⟨0,0,true⟩⟩, ⟨(-113938574209124517162277),(-75959049472692411877326),true⟩, ⟨3233375836697696484475846,3347139088205909786813758,true⟩⟩
theorem rightPrimalR007Q00P_ok : rightPrimalR007Q00P.encloses (primalThetaParameters rightPrimalR007Q00T (Grid.ofRats (97/100) (49/50))) := by decide +kernel

def rightPrimalR007Q00U : ℕ → ℚ
  | 0 => (-312/125)
  | 1 => (-9/4)
  | 2 => (-1851/1000)
  | 3 => (-1521/1000)
  | 4 => (-707/500)
  | 5 => (-1583/1000)
  | 6 => (-971/500)
  | 7 => (-2307/1000)
  | _ => 0
theorem rightPrimalR007Q00Sample0 : primalSampleCheck rightPrimalR007Q00T rightPrimalR007Q00P 0 (rightPrimalR007Q00U 0)=true := by decide +kernel
theorem rightPrimalR007Q00Sample1 : primalSampleCheck rightPrimalR007Q00T rightPrimalR007Q00P 1 (rightPrimalR007Q00U 1)=true := by decide +kernel
theorem rightPrimalR007Q00Sample2 : primalSampleCheck rightPrimalR007Q00T rightPrimalR007Q00P 2 (rightPrimalR007Q00U 2)=true := by decide +kernel
theorem rightPrimalR007Q00Sample3 : primalSampleCheck rightPrimalR007Q00T rightPrimalR007Q00P 3 (rightPrimalR007Q00U 3)=true := by decide +kernel
theorem rightPrimalR007Q00Sample4 : primalSampleCheck rightPrimalR007Q00T rightPrimalR007Q00P 4 (rightPrimalR007Q00U 4)=true := by decide +kernel
theorem rightPrimalR007Q00Sample5 : primalSampleCheck rightPrimalR007Q00T rightPrimalR007Q00P 5 (rightPrimalR007Q00U 5)=true := by decide +kernel
theorem rightPrimalR007Q00Sample6 : primalSampleCheck rightPrimalR007Q00T rightPrimalR007Q00P 6 (rightPrimalR007Q00U 6)=true := by decide +kernel
theorem rightPrimalR007Q00Sample7 : primalSampleCheck rightPrimalR007Q00T rightPrimalR007Q00P 7 (rightPrimalR007Q00U 7)=true := by decide +kernel

theorem rightPrimalR007Q00_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((97/100):ℝ)≤a) (au : a≤((49/50):ℝ)) : thetaHorizontalPeriod t a≤(((-37698701175115388651451622505/19807040628566084398385987584):ℚ):ℝ) := by
  have Tmem : rightPrimalR007Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR007Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR007Q00U
  · intro k
    fin_cases k
    · exact rightPrimalR007Q00Sample0
    · exact rightPrimalR007Q00Sample1
    · exact rightPrimalR007Q00Sample2
    · exact rightPrimalR007Q00Sample3
    · exact rightPrimalR007Q00Sample4
    · exact rightPrimalR007Q00Sample5
    · exact rightPrimalR007Q00Sample6
    · exact rightPrimalR007Q00Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR007Q00_period_bound
