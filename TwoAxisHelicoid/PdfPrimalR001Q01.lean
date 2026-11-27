import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR001Q01T := Grid.ofRats (7/5) (281/200)
def rightPrimalR001Q01P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1737563256688590540970676,1747058137872750106904937,true⟩,⟨0,0,true⟩⟩, ⟨(-322825960259123139106104),(-303836197890872726724415),true⟩, ⟨3305043396823036655410862,3365835565556071505160355,true⟩⟩
theorem rightPrimalR001Q01P_ok : rightPrimalR001Q01P.encloses (primalThetaParameters rightPrimalR001Q01T (Grid.ofRats (183/200) (23/25))) := by decide +kernel

def rightPrimalR001Q01U : ℕ → ℚ
  | 0 => (-1259/500)
  | 1 => (-1081/500)
  | 2 => (-877/500)
  | 3 => (-301/200)
  | 4 => (-1519/1000)
  | 5 => (-1799/1000)
  | 6 => (-1099/500)
  | 7 => (-2497/1000)
  | _ => 0
theorem rightPrimalR001Q01Sample0 : primalSampleCheck rightPrimalR001Q01T rightPrimalR001Q01P 0 (rightPrimalR001Q01U 0)=true := by decide +kernel
theorem rightPrimalR001Q01Sample1 : primalSampleCheck rightPrimalR001Q01T rightPrimalR001Q01P 1 (rightPrimalR001Q01U 1)=true := by decide +kernel
theorem rightPrimalR001Q01Sample2 : primalSampleCheck rightPrimalR001Q01T rightPrimalR001Q01P 2 (rightPrimalR001Q01U 2)=true := by decide +kernel
theorem rightPrimalR001Q01Sample3 : primalSampleCheck rightPrimalR001Q01T rightPrimalR001Q01P 3 (rightPrimalR001Q01U 3)=true := by decide +kernel
theorem rightPrimalR001Q01Sample4 : primalSampleCheck rightPrimalR001Q01T rightPrimalR001Q01P 4 (rightPrimalR001Q01U 4)=true := by decide +kernel
theorem rightPrimalR001Q01Sample5 : primalSampleCheck rightPrimalR001Q01T rightPrimalR001Q01P 5 (rightPrimalR001Q01U 5)=true := by decide +kernel
theorem rightPrimalR001Q01Sample6 : primalSampleCheck rightPrimalR001Q01T rightPrimalR001Q01P 6 (rightPrimalR001Q01U 6)=true := by decide +kernel
theorem rightPrimalR001Q01Sample7 : primalSampleCheck rightPrimalR001Q01T rightPrimalR001Q01P 7 (rightPrimalR001Q01U 7)=true := by decide +kernel

theorem rightPrimalR001Q01_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((183/200):ℝ)≤a) (au : a≤((23/25):ℝ)) : thetaHorizontalPeriod t a≤(((-18979693138327219468140223759/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR001Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR001Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR001Q01U
  · intro k
    fin_cases k
    · exact rightPrimalR001Q01Sample0
    · exact rightPrimalR001Q01Sample1
    · exact rightPrimalR001Q01Sample2
    · exact rightPrimalR001Q01Sample3
    · exact rightPrimalR001Q01Sample4
    · exact rightPrimalR001Q01Sample5
    · exact rightPrimalR001Q01Sample6
    · exact rightPrimalR001Q01Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR001Q01_period_bound
