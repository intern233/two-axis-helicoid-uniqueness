import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR002Q11T := Grid.ofRats (281/200) (141/100)
def rightPrimalR002Q11P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1756553019056772233874598,1766047900240931799808922,true⟩,⟨0,0,true⟩⟩, ⟨(-284846435522759753298138),(-265856673154509340916566),true⟩, ⟨3288898226952264206902566,3349138300083248572521262,true⟩⟩
theorem rightPrimalR002Q11P_ok : rightPrimalR002Q11P.encloses (primalThetaParameters rightPrimalR002Q11T (Grid.ofRats (37/40) (93/100))) := by decide +kernel

def rightPrimalR002Q11U : ℕ → ℚ
  | 0 => (-101/40)
  | 1 => (-1097/500)
  | 2 => (-1793/1000)
  | 3 => (-1533/1000)
  | 4 => (-1527/1000)
  | 5 => (-893/500)
  | 6 => (-1087/500)
  | 7 => (-62/25)
  | _ => 0
theorem rightPrimalR002Q11Sample0 : primalSampleCheck rightPrimalR002Q11T rightPrimalR002Q11P 0 (rightPrimalR002Q11U 0)=true := by decide +kernel
theorem rightPrimalR002Q11Sample1 : primalSampleCheck rightPrimalR002Q11T rightPrimalR002Q11P 1 (rightPrimalR002Q11U 1)=true := by decide +kernel
theorem rightPrimalR002Q11Sample2 : primalSampleCheck rightPrimalR002Q11T rightPrimalR002Q11P 2 (rightPrimalR002Q11U 2)=true := by decide +kernel
theorem rightPrimalR002Q11Sample3 : primalSampleCheck rightPrimalR002Q11T rightPrimalR002Q11P 3 (rightPrimalR002Q11U 3)=true := by decide +kernel
theorem rightPrimalR002Q11Sample4 : primalSampleCheck rightPrimalR002Q11T rightPrimalR002Q11P 4 (rightPrimalR002Q11U 4)=true := by decide +kernel
theorem rightPrimalR002Q11Sample5 : primalSampleCheck rightPrimalR002Q11T rightPrimalR002Q11P 5 (rightPrimalR002Q11U 5)=true := by decide +kernel
theorem rightPrimalR002Q11Sample6 : primalSampleCheck rightPrimalR002Q11T rightPrimalR002Q11P 6 (rightPrimalR002Q11U 6)=true := by decide +kernel
theorem rightPrimalR002Q11Sample7 : primalSampleCheck rightPrimalR002Q11T rightPrimalR002Q11P 7 (rightPrimalR002Q11U 7)=true := by decide +kernel

theorem rightPrimalR002Q11_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((37/40):ℝ)≤a) (au : a≤((93/100):ℝ)) : thetaHorizontalPeriod t a≤(((-19252337796145798026842605589/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR002Q11T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR002Q11P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR002Q11U
  · intro k
    fin_cases k
    · exact rightPrimalR002Q11Sample0
    · exact rightPrimalR002Q11Sample1
    · exact rightPrimalR002Q11Sample2
    · exact rightPrimalR002Q11Sample3
    · exact rightPrimalR002Q11Sample4
    · exact rightPrimalR002Q11Sample5
    · exact rightPrimalR002Q11Sample6
    · exact rightPrimalR002Q11Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR002Q11_period_bound
