import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR003Q11T := Grid.ofRats (281/200) (141/100)
def rightPrimalR003Q11P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1775542781424953926778523,1785037662609113492712907,true⟩,⟨0,0,true⟩⟩, ⟨(-246866910786396367490168),(-227877148418145955108718),true⟩, ⟨3279033393093082161127982,3338970879334673898915906,true⟩⟩
theorem rightPrimalR003Q11P_ok : rightPrimalR003Q11P.encloses (primalThetaParameters rightPrimalR003Q11T (Grid.ofRats (187/200) (47/50))) := by decide +kernel

def rightPrimalR003Q11U : ℕ → ℚ
  | 0 => (-1267/500)
  | 1 => (-2223/1000)
  | 2 => (-228/125)
  | 3 => (-1551/1000)
  | 4 => (-381/250)
  | 5 => (-883/500)
  | 6 => (-537/250)
  | 7 => (-493/200)
  | _ => 0
theorem rightPrimalR003Q11Sample0 : primalSampleCheck rightPrimalR003Q11T rightPrimalR003Q11P 0 (rightPrimalR003Q11U 0)=true := by decide +kernel
theorem rightPrimalR003Q11Sample1 : primalSampleCheck rightPrimalR003Q11T rightPrimalR003Q11P 1 (rightPrimalR003Q11U 1)=true := by decide +kernel
theorem rightPrimalR003Q11Sample2 : primalSampleCheck rightPrimalR003Q11T rightPrimalR003Q11P 2 (rightPrimalR003Q11U 2)=true := by decide +kernel
theorem rightPrimalR003Q11Sample3 : primalSampleCheck rightPrimalR003Q11T rightPrimalR003Q11P 3 (rightPrimalR003Q11U 3)=true := by decide +kernel
theorem rightPrimalR003Q11Sample4 : primalSampleCheck rightPrimalR003Q11T rightPrimalR003Q11P 4 (rightPrimalR003Q11U 4)=true := by decide +kernel
theorem rightPrimalR003Q11Sample5 : primalSampleCheck rightPrimalR003Q11T rightPrimalR003Q11P 5 (rightPrimalR003Q11U 5)=true := by decide +kernel
theorem rightPrimalR003Q11Sample6 : primalSampleCheck rightPrimalR003Q11T rightPrimalR003Q11P 6 (rightPrimalR003Q11U 6)=true := by decide +kernel
theorem rightPrimalR003Q11Sample7 : primalSampleCheck rightPrimalR003Q11T rightPrimalR003Q11P 7 (rightPrimalR003Q11U 7)=true := by decide +kernel

theorem rightPrimalR003Q11_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((187/200):ℝ)≤a) (au : a≤((47/50):ℝ)) : thetaHorizontalPeriod t a≤(((-19388335322621179734218904363/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR003Q11T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR003Q11P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR003Q11U
  · intro k
    fin_cases k
    · exact rightPrimalR003Q11Sample0
    · exact rightPrimalR003Q11Sample1
    · exact rightPrimalR003Q11Sample2
    · exact rightPrimalR003Q11Sample3
    · exact rightPrimalR003Q11Sample4
    · exact rightPrimalR003Q11Sample5
    · exact rightPrimalR003Q11Sample6
    · exact rightPrimalR003Q11Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR003Q11_period_bound
