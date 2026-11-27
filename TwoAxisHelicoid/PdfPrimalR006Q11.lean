import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR006Q11T := Grid.ofRats (281/200) (141/100)
def rightPrimalR006Q11P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1832512068529499005490294,1842006949713658571424860,true⟩,⟨0,0,true⟩⟩, ⟨(-132928336577306210066262),(-113938574209055797685175),true⟩, ⟨3258378238365721796570069,3317630041632890572318097,true⟩⟩
theorem rightPrimalR006Q11P_ok : rightPrimalR006Q11P.encloses (primalThetaParameters rightPrimalR006Q11T (Grid.ofRats (193/200) (97/100))) := by decide +kernel

def rightPrimalR006Q11U : ℕ → ℚ
  | 0 => (-1277/500)
  | 1 => (-2309/1000)
  | 2 => (-961/500)
  | 3 => (-403/250)
  | 4 => (-191/125)
  | 5 => (-429/250)
  | 6 => (-2077/1000)
  | 7 => (-2421/1000)
  | _ => 0
theorem rightPrimalR006Q11Sample0 : primalSampleCheck rightPrimalR006Q11T rightPrimalR006Q11P 0 (rightPrimalR006Q11U 0)=true := by decide +kernel
theorem rightPrimalR006Q11Sample1 : primalSampleCheck rightPrimalR006Q11T rightPrimalR006Q11P 1 (rightPrimalR006Q11U 1)=true := by decide +kernel
theorem rightPrimalR006Q11Sample2 : primalSampleCheck rightPrimalR006Q11T rightPrimalR006Q11P 2 (rightPrimalR006Q11U 2)=true := by decide +kernel
theorem rightPrimalR006Q11Sample3 : primalSampleCheck rightPrimalR006Q11T rightPrimalR006Q11P 3 (rightPrimalR006Q11U 3)=true := by decide +kernel
theorem rightPrimalR006Q11Sample4 : primalSampleCheck rightPrimalR006Q11T rightPrimalR006Q11P 4 (rightPrimalR006Q11U 4)=true := by decide +kernel
theorem rightPrimalR006Q11Sample5 : primalSampleCheck rightPrimalR006Q11T rightPrimalR006Q11P 5 (rightPrimalR006Q11U 5)=true := by decide +kernel
theorem rightPrimalR006Q11Sample6 : primalSampleCheck rightPrimalR006Q11T rightPrimalR006Q11P 6 (rightPrimalR006Q11U 6)=true := by decide +kernel
theorem rightPrimalR006Q11Sample7 : primalSampleCheck rightPrimalR006Q11T rightPrimalR006Q11P 7 (rightPrimalR006Q11U 7)=true := by decide +kernel

theorem rightPrimalR006Q11_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((193/200):ℝ)≤a) (au : a≤((97/100):ℝ)) : thetaHorizontalPeriod t a≤(((-19042016524540244183430618433/9903520314283042199192993792):ℚ):ℝ) := by
  have Tmem : rightPrimalR006Q11T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR006Q11P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR006Q11U
  · intro k
    fin_cases k
    · exact rightPrimalR006Q11Sample0
    · exact rightPrimalR006Q11Sample1
    · exact rightPrimalR006Q11Sample2
    · exact rightPrimalR006Q11Sample3
    · exact rightPrimalR006Q11Sample4
    · exact rightPrimalR006Q11Sample5
    · exact rightPrimalR006Q11Sample6
    · exact rightPrimalR006Q11Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR006Q11_period_bound
