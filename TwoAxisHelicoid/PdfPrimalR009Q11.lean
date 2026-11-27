import TwoAxisHelicoid.PdfPrimalEndpointBounds
import TwoAxisHelicoid.PdfPrimalParameterBox
import TwoAxisHelicoid.PdfRightOriginalStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rightPrimalR009Q11T := Grid.ofRats (281/200) (141/100)
def rightPrimalR009Q11P : PrimalThetaParameters := ⟨⟨⟨14408839182133102165303,14636959662350437303414,true⟩,⟨0,0,true⟩⟩, ⟨⟨1889481355634044084202067,1898976236818203650136812,true⟩,⟨0,0,true⟩⟩, ⟨(-18989762368216052642353),34359738368,true⟩, ⟨3250872436165900744503178,3309761738132128994954074,true⟩⟩
theorem rightPrimalR009Q11P_ok : rightPrimalR009Q11P.encloses (primalThetaParameters rightPrimalR009Q11T (Grid.ofRats (199/200) 1)) := by decide +kernel

def rightPrimalR009Q11U : ℕ → ℚ
  | 0 => (-321/125)
  | 1 => (-2393/1000)
  | 2 => (-1013/500)
  | 3 => (-843/500)
  | 4 => (-1547/1000)
  | 5 => (-1679/1000)
  | 6 => (-2013/1000)
  | 7 => (-2377/1000)
  | _ => 0
theorem rightPrimalR009Q11Sample0 : primalSampleCheck rightPrimalR009Q11T rightPrimalR009Q11P 0 (rightPrimalR009Q11U 0)=true := by decide +kernel
theorem rightPrimalR009Q11Sample1 : primalSampleCheck rightPrimalR009Q11T rightPrimalR009Q11P 1 (rightPrimalR009Q11U 1)=true := by decide +kernel
theorem rightPrimalR009Q11Sample2 : primalSampleCheck rightPrimalR009Q11T rightPrimalR009Q11P 2 (rightPrimalR009Q11U 2)=true := by decide +kernel
theorem rightPrimalR009Q11Sample3 : primalSampleCheck rightPrimalR009Q11T rightPrimalR009Q11P 3 (rightPrimalR009Q11U 3)=true := by decide +kernel
theorem rightPrimalR009Q11Sample4 : primalSampleCheck rightPrimalR009Q11T rightPrimalR009Q11P 4 (rightPrimalR009Q11U 4)=true := by decide +kernel
theorem rightPrimalR009Q11Sample5 : primalSampleCheck rightPrimalR009Q11T rightPrimalR009Q11P 5 (rightPrimalR009Q11U 5)=true := by decide +kernel
theorem rightPrimalR009Q11Sample6 : primalSampleCheck rightPrimalR009Q11T rightPrimalR009Q11P 6 (rightPrimalR009Q11U 6)=true := by decide +kernel
theorem rightPrimalR009Q11Sample7 : primalSampleCheck rightPrimalR009Q11T rightPrimalR009Q11P 7 (rightPrimalR009Q11U 7)=true := by decide +kernel

theorem rightPrimalR009Q11_period_bound {t a : ℝ} (tl : ((281/200):ℝ)≤t) (tu : t≤((141/100):ℝ)) (al : ((199/200):ℝ)≤a) (au : a≤(1:ℝ)) : thetaHorizontalPeriod t a≤(((-9705314663351274067227357767/4951760157141521099596496896):ℚ):ℝ) := by
  have Tmem : rightPrimalR009Q11T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have data := primal_box_parameters_sound rightPrimalR009Q11P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply primal_eight_point_upper Tmem data (by linarith) (right_original_full_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) rightPrimalR009Q11U
  · intro k
    fin_cases k
    · exact rightPrimalR009Q11Sample0
    · exact rightPrimalR009Q11Sample1
    · exact rightPrimalR009Q11Sample2
    · exact rightPrimalR009Q11Sample3
    · exact rightPrimalR009Q11Sample4
    · exact rightPrimalR009Q11Sample5
    · exact rightPrimalR009Q11Sample6
    · exact rightPrimalR009Q11Sample7
  · decide +kernel

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.rightPrimalR009Q11_period_bound
