import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR003Q01T := Grid.ofRats (7/5) (281/200)
def rightPrimalR003Q01P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1775542781424953926778523,1785037662609113492712907,true⟩,⟨0,0,true⟩⟩, ⟨(-246866910786396367490168),(-227877148418145955108718),true⟩, ⟨3283799256895618522499031,3343946050934198786242443,true⟩⟩
theorem rightPrimalR003Q01P_ok : rightPrimalR003Q01P.encloses (primalThetaParameters rightPrimalR003Q01T (Grid.ofRats (187/200) (47/50))) := by decide +kernel

def rightPrimalR003Q01U : ℕ → ℚ
  | 0 => (-2537/1000)
  | 1 => (-2221/1000)
  | 2 => (-227/125)
  | 3 => (-1539/1000)
  | 4 => (-1513/1000)
  | 5 => (-1757/1000)
  | 6 => (-1073/500)
  | 7 => (-2467/1000)
  | _ => 0
theorem rightPrimalR003Q01Sample0 : primalSampleCheck rightPrimalR003Q01T rightPrimalR003Q01P 0 (rightPrimalR003Q01U 0)=true := by decide +kernel
theorem rightPrimalR003Q01Sample1 : primalSampleCheck rightPrimalR003Q01T rightPrimalR003Q01P 1 (rightPrimalR003Q01U 1)=true := by decide +kernel
theorem rightPrimalR003Q01Sample2 : primalSampleCheck rightPrimalR003Q01T rightPrimalR003Q01P 2 (rightPrimalR003Q01U 2)=true := by decide +kernel
theorem rightPrimalR003Q01Sample3 : primalSampleCheck rightPrimalR003Q01T rightPrimalR003Q01P 3 (rightPrimalR003Q01U 3)=true := by decide +kernel
theorem rightPrimalR003Q01Sample4 : primalSampleCheck rightPrimalR003Q01T rightPrimalR003Q01P 4 (rightPrimalR003Q01U 4)=true := by decide +kernel
theorem rightPrimalR003Q01Sample5 : primalSampleCheck rightPrimalR003Q01T rightPrimalR003Q01P 5 (rightPrimalR003Q01U 5)=true := by decide +kernel
theorem rightPrimalR003Q01Sample6 : primalSampleCheck rightPrimalR003Q01T rightPrimalR003Q01P 6 (rightPrimalR003Q01U 6)=true := by decide +kernel
theorem rightPrimalR003Q01Sample7 : primalSampleCheck rightPrimalR003Q01T rightPrimalR003Q01P 7 (rightPrimalR003Q01U 7)=true := by decide +kernel

theorem rightPrimalR003Q01_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((187/200):ℝ)≤a) (au : a≤((47/50):ℝ)) : thetaHorizontalPeriod t a≤(((-19388335322621179734218904363/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR003Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR003Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR003Q01U
  · intro k
    fin_cases k
    · exact rightPrimalR003Q01Sample0
    · exact rightPrimalR003Q01Sample1
    · exact rightPrimalR003Q01Sample2
    · exact rightPrimalR003Q01Sample3
    · exact rightPrimalR003Q01Sample4
    · exact rightPrimalR003Q01Sample5
    · exact rightPrimalR003Q01Sample6
    · exact rightPrimalR003Q01Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR003Q01_period_bound
