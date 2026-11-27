import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR006Q01T := Grid.ofRats (7/5) (281/200)
def rightPrimalR006Q01P : PrimalThetaParameters := ⟨⟨⟨14636959662281717826405,14868691741796214871495,true⟩,⟨0,0,true⟩⟩, ⟨⟨1832512068529499005490294,1842006949713658571424860,true⟩,⟨0,0,true⟩⟩, ⟨(-132928336577306210066262),(-113938574209055797685175),true⟩, ⟨3263150687425771848814479,3322608720522499789447840,true⟩⟩
theorem rightPrimalR006Q01P_ok : rightPrimalR006Q01P.encloses (primalThetaParameters rightPrimalR006Q01T (Grid.ofRats (193/200) (97/100))) := by decide +kernel

def rightPrimalR006Q01U : ℕ → ℚ
  | 0 => (-1279/500)
  | 1 => (-577/250)
  | 2 => (-383/200)
  | 3 => (-1601/1000)
  | 4 => (-379/250)
  | 5 => (-1707/1000)
  | 6 => (-2073/1000)
  | 7 => (-2423/1000)
  | _ => 0
theorem rightPrimalR006Q01Sample0 : primalSampleCheck rightPrimalR006Q01T rightPrimalR006Q01P 0 (rightPrimalR006Q01U 0)=true := by decide +kernel
theorem rightPrimalR006Q01Sample1 : primalSampleCheck rightPrimalR006Q01T rightPrimalR006Q01P 1 (rightPrimalR006Q01U 1)=true := by decide +kernel
theorem rightPrimalR006Q01Sample2 : primalSampleCheck rightPrimalR006Q01T rightPrimalR006Q01P 2 (rightPrimalR006Q01U 2)=true := by decide +kernel
theorem rightPrimalR006Q01Sample3 : primalSampleCheck rightPrimalR006Q01T rightPrimalR006Q01P 3 (rightPrimalR006Q01U 3)=true := by decide +kernel
theorem rightPrimalR006Q01Sample4 : primalSampleCheck rightPrimalR006Q01T rightPrimalR006Q01P 4 (rightPrimalR006Q01U 4)=true := by decide +kernel
theorem rightPrimalR006Q01Sample5 : primalSampleCheck rightPrimalR006Q01T rightPrimalR006Q01P 5 (rightPrimalR006Q01U 5)=true := by decide +kernel
theorem rightPrimalR006Q01Sample6 : primalSampleCheck rightPrimalR006Q01T rightPrimalR006Q01P 6 (rightPrimalR006Q01U 6)=true := by decide +kernel
theorem rightPrimalR006Q01Sample7 : primalSampleCheck rightPrimalR006Q01T rightPrimalR006Q01P 7 (rightPrimalR006Q01U 7)=true := by decide +kernel

theorem rightPrimalR006Q01_period_bound {t a : ℝ} (tl : ((7/5):ℝ)≤t) (tu : t≤((281/200):ℝ)) (al : ((193/200):ℝ)≤a) (au : a≤((97/100):ℝ)) : thetaHorizontalPeriod t a≤(((-19042016524540244183430618433/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR006Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR006Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR006Q01U
  · intro k
    fin_cases k
    · exact rightPrimalR006Q01Sample0
    · exact rightPrimalR006Q01Sample1
    · exact rightPrimalR006Q01Sample2
    · exact rightPrimalR006Q01Sample3
    · exact rightPrimalR006Q01Sample4
    · exact rightPrimalR006Q01Sample5
    · exact rightPrimalR006Q01Sample6
    · exact rightPrimalR006Q01Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR006Q01_period_bound
