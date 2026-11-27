import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR002Q01T := Grid.ofRats (7/5) (281/200)
def rightPrimalR002Q01P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1756553019056772233874598,1766047900240931799808922,true⟩,⟨0,0,true⟩⟩, ⟨(-284846435522759753298138),(-265856673154509340916566),true⟩, ⟨3293661193032028221793952,3354111601230082605752489,true⟩⟩
theorem rightPrimalR002Q01P_ok : rightPrimalR002Q01P.encloses (primalThetaParameters rightPrimalR002Q01T (Grid.ofRats (37/40) (93/100))) := by decide +kernel

def rightPrimalR002Q01U : ℕ → ℚ
  | 0 => (-316/125)
  | 1 => (-2191/1000)
  | 2 => (-357/200)
  | 3 => (-1521/1000)
  | 4 => (-303/200)
  | 5 => (-1777/1000)
  | 6 => (-543/250)
  | 7 => (-1241/500)
  | _ => 0
theorem rightPrimalR002Q01Sample0 : primalSampleCheck rightPrimalR002Q01T rightPrimalR002Q01P 0 (rightPrimalR002Q01U 0)=true := by decide +kernel
theorem rightPrimalR002Q01Sample1 : primalSampleCheck rightPrimalR002Q01T rightPrimalR002Q01P 1 (rightPrimalR002Q01U 1)=true := by decide +kernel
theorem rightPrimalR002Q01Sample2 : primalSampleCheck rightPrimalR002Q01T rightPrimalR002Q01P 2 (rightPrimalR002Q01U 2)=true := by decide +kernel
theorem rightPrimalR002Q01Sample3 : primalSampleCheck rightPrimalR002Q01T rightPrimalR002Q01P 3 (rightPrimalR002Q01U 3)=true := by decide +kernel
theorem rightPrimalR002Q01Sample4 : primalSampleCheck rightPrimalR002Q01T rightPrimalR002Q01P 4 (rightPrimalR002Q01U 4)=true := by decide +kernel
theorem rightPrimalR002Q01Sample5 : primalSampleCheck rightPrimalR002Q01T rightPrimalR002Q01P 5 (rightPrimalR002Q01U 5)=true := by decide +kernel
theorem rightPrimalR002Q01Sample6 : primalSampleCheck rightPrimalR002Q01T rightPrimalR002Q01P 6 (rightPrimalR002Q01U 6)=true := by decide +kernel
theorem rightPrimalR002Q01Sample7 : primalSampleCheck rightPrimalR002Q01T rightPrimalR002Q01P 7 (rightPrimalR002Q01U 7)=true := by decide +kernel

theorem rightPrimalR002Q01_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((37/40):ℝ)≤a) (au : a≤((93/100):ℝ)) : thetaHorizontalPeriod t a≤(((-19252337796145798026842605589/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR002Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR002Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR002Q01U
  · intro k
    fin_cases k
    · exact rightPrimalR002Q01Sample0
    · exact rightPrimalR002Q01Sample1
    · exact rightPrimalR002Q01Sample2
    · exact rightPrimalR002Q01Sample3
    · exact rightPrimalR002Q01Sample4
    · exact rightPrimalR002Q01Sample5
    · exact rightPrimalR002Q01Sample6
    · exact rightPrimalR002Q01Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR002Q01_period_bound
