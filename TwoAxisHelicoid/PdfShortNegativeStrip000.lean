import TwoAxisHelicoid.PdfBoundedNegativeStrip
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeStrip000T := Grid.ofRats (9/10) (37/40)
def shortNegativeStrip000P : PrimalThetaParameters := ⟨⟨⟨66122844173083764062562,71525505308326081390643,true⟩,⟨0,0,true⟩⟩, ⟨⟨1147703033094108932088756,1167406034418893553203191,true⟩,⟨0,0,true⟩⟩, ⟨(-1502546407448086356873700),(-1463140404798585834124217),true⟩, ⟨5659634632975839708554358,6112302455914648369756111,true⟩⟩
theorem shortNegativeStrip000P_ok : shortNegativeStrip000P.encloses (primalThetaParameters shortNegativeStrip000T (Grid.ofRats (996784061054281/1649267441664000) (1013896185976057/1649267441664000))) := by decide +kernel

theorem shortNegativeStrip000Edge0false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 0 false := by decide +kernel
theorem shortNegativeStrip000Edge0true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 0 true := by decide +kernel
theorem shortNegativeStrip000Edge1false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 1 false := by decide +kernel
theorem shortNegativeStrip000Edge1true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 1 true := by decide +kernel
theorem shortNegativeStrip000Edge2false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 2 false := by decide +kernel
theorem shortNegativeStrip000Edge2true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 2 true := by decide +kernel
theorem shortNegativeStrip000Edge3false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 3 false := by decide +kernel
theorem shortNegativeStrip000Edge3true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 3 true := by decide +kernel
theorem shortNegativeStrip000Edge4false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 4 false := by decide +kernel
theorem shortNegativeStrip000Edge4true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 4 true := by decide +kernel
theorem shortNegativeStrip000Edge5false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 5 false := by decide +kernel
theorem shortNegativeStrip000Edge5true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 5 true := by decide +kernel
theorem shortNegativeStrip000Edge6false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 6 false := by decide +kernel
theorem shortNegativeStrip000Edge6true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 6 true := by decide +kernel
theorem shortNegativeStrip000Edge7false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 7 false := by decide +kernel
theorem shortNegativeStrip000Edge7true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 7 true := by decide +kernel
theorem shortNegativeStrip000Edge8false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 8 false := by decide +kernel
theorem shortNegativeStrip000Edge8true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 8 true := by decide +kernel
theorem shortNegativeStrip000Edge9false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 9 false := by decide +kernel
theorem shortNegativeStrip000Edge9true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 9 true := by decide +kernel
theorem shortNegativeStrip000Edge10false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 10 false := by decide +kernel
theorem shortNegativeStrip000Edge10true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 10 true := by decide +kernel
theorem shortNegativeStrip000Edge11false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 11 false := by decide +kernel
theorem shortNegativeStrip000Edge11true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 11 true := by decide +kernel
theorem shortNegativeStrip000Edge12false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 12 false := by decide +kernel
theorem shortNegativeStrip000Edge12true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 12 true := by decide +kernel
theorem shortNegativeStrip000Edge13false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 13 false := by decide +kernel
theorem shortNegativeStrip000Edge13true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 13 true := by decide +kernel
theorem shortNegativeStrip000Edge14false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 14 false := by decide +kernel
theorem shortNegativeStrip000Edge14true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 14 true := by decide +kernel
theorem shortNegativeStrip000Edge15false : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 15 false := by decide +kernel
theorem shortNegativeStrip000Edge15true : boundedNegativeEdgeCheck 17310 shortNegativeStrip000T shortNegativeStrip000P 15 true := by decide +kernel
theorem shortNegativeStrip000Bound {t a : ℝ} (tl : ((9/10):ℝ)≤t) (tu : t≤((37/40):ℝ)) (al : ((996784061054281/1649267441664000):ℝ)≤a) (au : a≤((1013896185976057/1649267441664000):ℝ)) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤(17310:ℝ) := by
  have ts : shortNegativeStrip000T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have ps := primal_box_parameters_sound shortNegativeStrip000P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply bounded_negative_strip_of_grid (M:=17310) ts ps (by linarith)
  intro k flag
  fin_cases k <;> cases flag
  · exact shortNegativeStrip000Edge0false
  · exact shortNegativeStrip000Edge0true
  · exact shortNegativeStrip000Edge1false
  · exact shortNegativeStrip000Edge1true
  · exact shortNegativeStrip000Edge2false
  · exact shortNegativeStrip000Edge2true
  · exact shortNegativeStrip000Edge3false
  · exact shortNegativeStrip000Edge3true
  · exact shortNegativeStrip000Edge4false
  · exact shortNegativeStrip000Edge4true
  · exact shortNegativeStrip000Edge5false
  · exact shortNegativeStrip000Edge5true
  · exact shortNegativeStrip000Edge6false
  · exact shortNegativeStrip000Edge6true
  · exact shortNegativeStrip000Edge7false
  · exact shortNegativeStrip000Edge7true
  · exact shortNegativeStrip000Edge8false
  · exact shortNegativeStrip000Edge8true
  · exact shortNegativeStrip000Edge9false
  · exact shortNegativeStrip000Edge9true
  · exact shortNegativeStrip000Edge10false
  · exact shortNegativeStrip000Edge10true
  · exact shortNegativeStrip000Edge11false
  · exact shortNegativeStrip000Edge11true
  · exact shortNegativeStrip000Edge12false
  · exact shortNegativeStrip000Edge12true
  · exact shortNegativeStrip000Edge13false
  · exact shortNegativeStrip000Edge13true
  · exact shortNegativeStrip000Edge14false
  · exact shortNegativeStrip000Edge14true
  · exact shortNegativeStrip000Edge15false
  · exact shortNegativeStrip000Edge15true

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeStrip000Bound
