import TwoAxisHelicoid.PdfBoundedNegativeStrip
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeStrip056T := Grid.ofRats (137/100) (7/5)
def shortNegativeStrip056P : PrimalThetaParameters := ⟨⟨⟨14868691741727495394482,16338193991784627953815,true⟩,⟨0,0,true⟩⟩, ⟨⟨1670116902198393495049754,1799496973755180518125308,true⟩,⟨0,0,true⟩⟩, ⟨(-457718669239517230948377),(-198958526126011904284007),true⟩, ⟨2990865418750904019305079,3797925192089384253765071,true⟩⟩
theorem shortNegativeStrip056P_ok : shortNegativeStrip056P.encloses (primalThetaParameters shortNegativeStrip056T (Grid.ofRats (483500772181657/549755813888000) (520956452332099/549755813888000))) := by decide +kernel

theorem shortNegativeStrip056Edge0false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 0 false := by decide +kernel
theorem shortNegativeStrip056Edge0true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 0 true := by decide +kernel
theorem shortNegativeStrip056Edge1false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 1 false := by decide +kernel
theorem shortNegativeStrip056Edge1true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 1 true := by decide +kernel
theorem shortNegativeStrip056Edge2false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 2 false := by decide +kernel
theorem shortNegativeStrip056Edge2true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 2 true := by decide +kernel
theorem shortNegativeStrip056Edge3false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 3 false := by decide +kernel
theorem shortNegativeStrip056Edge3true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 3 true := by decide +kernel
theorem shortNegativeStrip056Edge4false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 4 false := by decide +kernel
theorem shortNegativeStrip056Edge4true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 4 true := by decide +kernel
theorem shortNegativeStrip056Edge5false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 5 false := by decide +kernel
theorem shortNegativeStrip056Edge5true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 5 true := by decide +kernel
theorem shortNegativeStrip056Edge6false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 6 false := by decide +kernel
theorem shortNegativeStrip056Edge6true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 6 true := by decide +kernel
theorem shortNegativeStrip056Edge7false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 7 false := by decide +kernel
theorem shortNegativeStrip056Edge7true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 7 true := by decide +kernel
theorem shortNegativeStrip056Edge8false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 8 false := by decide +kernel
theorem shortNegativeStrip056Edge8true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 8 true := by decide +kernel
theorem shortNegativeStrip056Edge9false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 9 false := by decide +kernel
theorem shortNegativeStrip056Edge9true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 9 true := by decide +kernel
theorem shortNegativeStrip056Edge10false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 10 false := by decide +kernel
theorem shortNegativeStrip056Edge10true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 10 true := by decide +kernel
theorem shortNegativeStrip056Edge11false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 11 false := by decide +kernel
theorem shortNegativeStrip056Edge11true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 11 true := by decide +kernel
theorem shortNegativeStrip056Edge12false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 12 false := by decide +kernel
theorem shortNegativeStrip056Edge12true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 12 true := by decide +kernel
theorem shortNegativeStrip056Edge13false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 13 false := by decide +kernel
theorem shortNegativeStrip056Edge13true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 13 true := by decide +kernel
theorem shortNegativeStrip056Edge14false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 14 false := by decide +kernel
theorem shortNegativeStrip056Edge14true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 14 true := by decide +kernel
theorem shortNegativeStrip056Edge15false : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 15 false := by decide +kernel
theorem shortNegativeStrip056Edge15true : boundedNegativeEdgeCheck 80 shortNegativeStrip056T shortNegativeStrip056P 15 true := by decide +kernel
theorem shortNegativeStrip056Bound {t a : ℝ} (tl : ((137/100):ℝ)≤t) (tu : t≤((7/5):ℝ)) (al : ((483500772181657/549755813888000):ℝ)≤a) (au : a≤((520956452332099/549755813888000):ℝ)) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤(80:ℝ) := by
  have ts : shortNegativeStrip056T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have ps := primal_box_parameters_sound shortNegativeStrip056P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply bounded_negative_strip_of_grid (M:=80) ts ps (by linarith)
  intro k flag
  fin_cases k <;> cases flag
  · exact shortNegativeStrip056Edge0false
  · exact shortNegativeStrip056Edge0true
  · exact shortNegativeStrip056Edge1false
  · exact shortNegativeStrip056Edge1true
  · exact shortNegativeStrip056Edge2false
  · exact shortNegativeStrip056Edge2true
  · exact shortNegativeStrip056Edge3false
  · exact shortNegativeStrip056Edge3true
  · exact shortNegativeStrip056Edge4false
  · exact shortNegativeStrip056Edge4true
  · exact shortNegativeStrip056Edge5false
  · exact shortNegativeStrip056Edge5true
  · exact shortNegativeStrip056Edge6false
  · exact shortNegativeStrip056Edge6true
  · exact shortNegativeStrip056Edge7false
  · exact shortNegativeStrip056Edge7true
  · exact shortNegativeStrip056Edge8false
  · exact shortNegativeStrip056Edge8true
  · exact shortNegativeStrip056Edge9false
  · exact shortNegativeStrip056Edge9true
  · exact shortNegativeStrip056Edge10false
  · exact shortNegativeStrip056Edge10true
  · exact shortNegativeStrip056Edge11false
  · exact shortNegativeStrip056Edge11true
  · exact shortNegativeStrip056Edge12false
  · exact shortNegativeStrip056Edge12true
  · exact shortNegativeStrip056Edge13false
  · exact shortNegativeStrip056Edge13true
  · exact shortNegativeStrip056Edge14false
  · exact shortNegativeStrip056Edge14true
  · exact shortNegativeStrip056Edge15false
  · exact shortNegativeStrip056Edge15true

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeStrip056Bound
