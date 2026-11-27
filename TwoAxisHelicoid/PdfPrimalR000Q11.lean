import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR000Q11T := Grid.ofRats (281/200) (141/100)
def rightPrimalR000Q11P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1718573494320408848066751,1728068375504568414000954,true⟩,⟨0,0,true⟩⟩, ⟨(-360805484995486524914074),(-341815722627236112532261),true⟩, ⟨3313212919456410019651407,3374173439912610126260804,true⟩⟩
theorem rightPrimalR000Q11P_ok : rightPrimalR000Q11P.encloses (primalThetaParameters rightPrimalR000Q11T (Grid.ofRats (181/200) (91/100))) := by decide +kernel

def rightPrimalR000Q11U : ℕ → ℚ
  | 0 => (-1253/500)
  | 1 => (-267/125)
  | 2 => (-867/500)
  | 3 => (-1503/1000)
  | 4 => (-192/125)
  | 5 => (-1829/1000)
  | 6 => (-557/250)
  | 7 => (-2509/1000)
  | _ => 0
theorem rightPrimalR000Q11Sample0 : primalSampleCheck rightPrimalR000Q11T rightPrimalR000Q11P 0 (rightPrimalR000Q11U 0)=true := by decide +kernel
theorem rightPrimalR000Q11Sample1 : primalSampleCheck rightPrimalR000Q11T rightPrimalR000Q11P 1 (rightPrimalR000Q11U 1)=true := by decide +kernel
theorem rightPrimalR000Q11Sample2 : primalSampleCheck rightPrimalR000Q11T rightPrimalR000Q11P 2 (rightPrimalR000Q11U 2)=true := by decide +kernel
theorem rightPrimalR000Q11Sample3 : primalSampleCheck rightPrimalR000Q11T rightPrimalR000Q11P 3 (rightPrimalR000Q11U 3)=true := by decide +kernel
theorem rightPrimalR000Q11Sample4 : primalSampleCheck rightPrimalR000Q11T rightPrimalR000Q11P 4 (rightPrimalR000Q11U 4)=true := by decide +kernel
theorem rightPrimalR000Q11Sample5 : primalSampleCheck rightPrimalR000Q11T rightPrimalR000Q11P 5 (rightPrimalR000Q11U 5)=true := by decide +kernel
theorem rightPrimalR000Q11Sample6 : primalSampleCheck rightPrimalR000Q11T rightPrimalR000Q11P 6 (rightPrimalR000Q11U 6)=true := by decide +kernel
theorem rightPrimalR000Q11Sample7 : primalSampleCheck rightPrimalR000Q11T rightPrimalR000Q11P 7 (rightPrimalR000Q11U 7)=true := by decide +kernel

theorem rightPrimalR000Q11_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((181/200):ℝ)≤a) (au : a≤((91/100):ℝ)) : thetaHorizontalPeriod t a≤(((-38221261534559097372905182055/19807040628566084398385987584):ℚ):ℝ) := by
  have Tmem : rightPrimalR000Q11T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR000Q11P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR000Q11U
  · intro k
    fin_cases k
    · exact rightPrimalR000Q11Sample0
    · exact rightPrimalR000Q11Sample1
    · exact rightPrimalR000Q11Sample2
    · exact rightPrimalR000Q11Sample3
    · exact rightPrimalR000Q11Sample4
    · exact rightPrimalR000Q11Sample5
    · exact rightPrimalR000Q11Sample6
    · exact rightPrimalR000Q11Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR000Q11_period_bound
