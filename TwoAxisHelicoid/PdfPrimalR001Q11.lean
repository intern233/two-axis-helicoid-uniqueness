import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR001Q11T := Grid.ofRats (281/200) (141/100)
def rightPrimalR001Q11P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1737563256688590540970676,1747058137872750106904937,true⟩,⟨0,0,true⟩⟩, ⟨(-322825960259123139106104),(-303836197890872726724415),true⟩, ⟨3300283675921503945097178,3360864479927527104995532,true⟩⟩
theorem rightPrimalR001Q11P_ok : rightPrimalR001Q11P.encloses (primalThetaParameters rightPrimalR001Q11T (Grid.ofRats (183/200) (23/25))) := by decide +kernel

def rightPrimalR001Q11U : ℕ → ℚ
  | 0 => (-629/250)
  | 1 => (-433/200)
  | 2 => (-1763/1000)
  | 3 => (-1517/1000)
  | 4 => (-1531/1000)
  | 5 => (-1807/1000)
  | 6 => (-11/5)
  | 7 => (-1247/500)
  | _ => 0
theorem rightPrimalR001Q11Sample0 : primalSampleCheck rightPrimalR001Q11T rightPrimalR001Q11P 0 (rightPrimalR001Q11U 0)=true := by decide +kernel
theorem rightPrimalR001Q11Sample1 : primalSampleCheck rightPrimalR001Q11T rightPrimalR001Q11P 1 (rightPrimalR001Q11U 1)=true := by decide +kernel
theorem rightPrimalR001Q11Sample2 : primalSampleCheck rightPrimalR001Q11T rightPrimalR001Q11P 2 (rightPrimalR001Q11U 2)=true := by decide +kernel
theorem rightPrimalR001Q11Sample3 : primalSampleCheck rightPrimalR001Q11T rightPrimalR001Q11P 3 (rightPrimalR001Q11U 3)=true := by decide +kernel
theorem rightPrimalR001Q11Sample4 : primalSampleCheck rightPrimalR001Q11T rightPrimalR001Q11P 4 (rightPrimalR001Q11U 4)=true := by decide +kernel
theorem rightPrimalR001Q11Sample5 : primalSampleCheck rightPrimalR001Q11T rightPrimalR001Q11P 5 (rightPrimalR001Q11U 5)=true := by decide +kernel
theorem rightPrimalR001Q11Sample6 : primalSampleCheck rightPrimalR001Q11T rightPrimalR001Q11P 6 (rightPrimalR001Q11U 6)=true := by decide +kernel
theorem rightPrimalR001Q11Sample7 : primalSampleCheck rightPrimalR001Q11T rightPrimalR001Q11P 7 (rightPrimalR001Q11U 7)=true := by decide +kernel

theorem rightPrimalR001Q11_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((183/200):ℝ)≤a) (au : a≤((23/25):ℝ)) : thetaHorizontalPeriod t a≤(((-18979693138327219468140223759/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR001Q11T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR001Q11P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR001Q11U
  · intro k
    fin_cases k
    · exact rightPrimalR001Q11Sample0
    · exact rightPrimalR001Q11Sample1
    · exact rightPrimalR001Q11Sample2
    · exact rightPrimalR001Q11Sample3
    · exact rightPrimalR001Q11Sample4
    · exact rightPrimalR001Q11Sample5
    · exact rightPrimalR001Q11Sample6
    · exact rightPrimalR001Q11Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR001Q11_period_bound
