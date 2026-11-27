import TwoAxisHelicoid.PdfBoundedNegativeStrip
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeStrip008T := Grid.ofRats (37/40) (97/100)
def shortNegativeStrip008P : PrimalThetaParameters := ⟨⟨⟨57405643536170928863480,66122844173152483540205,true⟩,⟨0,0,true⟩⟩, ⟨⟨1163392882874762148673025,1201026350732955241204760,true⟩,⟨0,0,true⟩⟩, ⟨(-1471166707886779923705062),(-1395899772170462458121293),true⟩, ⟨5247081405345110160460317,6008110121848525972506894,true⟩⟩
theorem shortNegativeStrip008P_ok : shortNegativeStrip008P.encloses (primalThetaParameters shortNegativeStrip008T (Grid.ofRats (202082149990879/329853488332800) (1043095547189831/1649267441664000))) := by decide +kernel

theorem shortNegativeStrip008Edge0false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 0 false := by decide +kernel
theorem shortNegativeStrip008Edge0true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 0 true := by decide +kernel
theorem shortNegativeStrip008Edge1false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 1 false := by decide +kernel
theorem shortNegativeStrip008Edge1true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 1 true := by decide +kernel
theorem shortNegativeStrip008Edge2false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 2 false := by decide +kernel
theorem shortNegativeStrip008Edge2true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 2 true := by decide +kernel
theorem shortNegativeStrip008Edge3false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 3 false := by decide +kernel
theorem shortNegativeStrip008Edge3true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 3 true := by decide +kernel
theorem shortNegativeStrip008Edge4false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 4 false := by decide +kernel
theorem shortNegativeStrip008Edge4true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 4 true := by decide +kernel
theorem shortNegativeStrip008Edge5false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 5 false := by decide +kernel
theorem shortNegativeStrip008Edge5true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 5 true := by decide +kernel
theorem shortNegativeStrip008Edge6false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 6 false := by decide +kernel
theorem shortNegativeStrip008Edge6true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 6 true := by decide +kernel
theorem shortNegativeStrip008Edge7false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 7 false := by decide +kernel
theorem shortNegativeStrip008Edge7true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 7 true := by decide +kernel
theorem shortNegativeStrip008Edge8false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 8 false := by decide +kernel
theorem shortNegativeStrip008Edge8true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 8 true := by decide +kernel
theorem shortNegativeStrip008Edge9false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 9 false := by decide +kernel
theorem shortNegativeStrip008Edge9true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 9 true := by decide +kernel
theorem shortNegativeStrip008Edge10false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 10 false := by decide +kernel
theorem shortNegativeStrip008Edge10true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 10 true := by decide +kernel
theorem shortNegativeStrip008Edge11false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 11 false := by decide +kernel
theorem shortNegativeStrip008Edge11true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 11 true := by decide +kernel
theorem shortNegativeStrip008Edge12false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 12 false := by decide +kernel
theorem shortNegativeStrip008Edge12true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 12 true := by decide +kernel
theorem shortNegativeStrip008Edge13false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 13 false := by decide +kernel
theorem shortNegativeStrip008Edge13true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 13 true := by decide +kernel
theorem shortNegativeStrip008Edge14false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 14 false := by decide +kernel
theorem shortNegativeStrip008Edge14true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 14 true := by decide +kernel
theorem shortNegativeStrip008Edge15false : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 15 false := by decide +kernel
theorem shortNegativeStrip008Edge15true : boundedNegativeEdgeCheck 17660 shortNegativeStrip008T shortNegativeStrip008P 15 true := by decide +kernel
theorem shortNegativeStrip008Bound {t a : ℝ} (tl : ((37/40):ℝ)≤t) (tu : t≤((97/100):ℝ)) (al : ((202082149990879/329853488332800):ℝ)≤a) (au : a≤((1043095547189831/1649267441664000):ℝ)) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤(17660:ℝ) := by
  have ts : shortNegativeStrip008T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have ps := primal_box_parameters_sound shortNegativeStrip008P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply bounded_negative_strip_of_grid (M:=17660) ts ps (by linarith)
  intro k flag
  fin_cases k <;> cases flag
  · exact shortNegativeStrip008Edge0false
  · exact shortNegativeStrip008Edge0true
  · exact shortNegativeStrip008Edge1false
  · exact shortNegativeStrip008Edge1true
  · exact shortNegativeStrip008Edge2false
  · exact shortNegativeStrip008Edge2true
  · exact shortNegativeStrip008Edge3false
  · exact shortNegativeStrip008Edge3true
  · exact shortNegativeStrip008Edge4false
  · exact shortNegativeStrip008Edge4true
  · exact shortNegativeStrip008Edge5false
  · exact shortNegativeStrip008Edge5true
  · exact shortNegativeStrip008Edge6false
  · exact shortNegativeStrip008Edge6true
  · exact shortNegativeStrip008Edge7false
  · exact shortNegativeStrip008Edge7true
  · exact shortNegativeStrip008Edge8false
  · exact shortNegativeStrip008Edge8true
  · exact shortNegativeStrip008Edge9false
  · exact shortNegativeStrip008Edge9true
  · exact shortNegativeStrip008Edge10false
  · exact shortNegativeStrip008Edge10true
  · exact shortNegativeStrip008Edge11false
  · exact shortNegativeStrip008Edge11true
  · exact shortNegativeStrip008Edge12false
  · exact shortNegativeStrip008Edge12true
  · exact shortNegativeStrip008Edge13false
  · exact shortNegativeStrip008Edge13true
  · exact shortNegativeStrip008Edge14false
  · exact shortNegativeStrip008Edge14true
  · exact shortNegativeStrip008Edge15false
  · exact shortNegativeStrip008Edge15true

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeStrip008Bound
