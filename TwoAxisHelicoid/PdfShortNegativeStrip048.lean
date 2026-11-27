import TwoAxisHelicoid.PdfBoundedNegativeStrip
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeStrip048T := Grid.ofRats (129/100) (137/100)
def shortNegativeStrip048P : PrimalThetaParameters := ⟨⟨⟨16338193991715908476779,21006522165043968233378,true⟩,⟨0,0,true⟩⟩, ⟨⟨1521153325496760728736050,1687577271887854761136540,true⟩,⟨0,0,true⟩⟩, ⟨(-755645822642782763576733),(-422797929860663418260830),true⟩, ⟨3024992227265157223279878,4229366323287399113687564,true⟩⟩
theorem shortNegativeStrip048P_ok : shortNegativeStrip048P.encloses (primalThetaParameters shortNegativeStrip048T (Grid.ofRats (1321126934018083/1649267441664000) (1465666708120709/1649267441664000))) := by decide +kernel

theorem shortNegativeStrip048Edge0false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 0 false := by decide +kernel
theorem shortNegativeStrip048Edge0true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 0 true := by decide +kernel
theorem shortNegativeStrip048Edge1false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 1 false := by decide +kernel
theorem shortNegativeStrip048Edge1true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 1 true := by decide +kernel
theorem shortNegativeStrip048Edge2false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 2 false := by decide +kernel
theorem shortNegativeStrip048Edge2true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 2 true := by decide +kernel
theorem shortNegativeStrip048Edge3false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 3 false := by decide +kernel
theorem shortNegativeStrip048Edge3true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 3 true := by decide +kernel
theorem shortNegativeStrip048Edge4false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 4 false := by decide +kernel
theorem shortNegativeStrip048Edge4true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 4 true := by decide +kernel
theorem shortNegativeStrip048Edge5false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 5 false := by decide +kernel
theorem shortNegativeStrip048Edge5true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 5 true := by decide +kernel
theorem shortNegativeStrip048Edge6false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 6 false := by decide +kernel
theorem shortNegativeStrip048Edge6true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 6 true := by decide +kernel
theorem shortNegativeStrip048Edge7false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 7 false := by decide +kernel
theorem shortNegativeStrip048Edge7true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 7 true := by decide +kernel
theorem shortNegativeStrip048Edge8false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 8 false := by decide +kernel
theorem shortNegativeStrip048Edge8true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 8 true := by decide +kernel
theorem shortNegativeStrip048Edge9false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 9 false := by decide +kernel
theorem shortNegativeStrip048Edge9true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 9 true := by decide +kernel
theorem shortNegativeStrip048Edge10false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 10 false := by decide +kernel
theorem shortNegativeStrip048Edge10true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 10 true := by decide +kernel
theorem shortNegativeStrip048Edge11false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 11 false := by decide +kernel
theorem shortNegativeStrip048Edge11true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 11 true := by decide +kernel
theorem shortNegativeStrip048Edge12false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 12 false := by decide +kernel
theorem shortNegativeStrip048Edge12true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 12 true := by decide +kernel
theorem shortNegativeStrip048Edge13false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 13 false := by decide +kernel
theorem shortNegativeStrip048Edge13true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 13 true := by decide +kernel
theorem shortNegativeStrip048Edge14false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 14 false := by decide +kernel
theorem shortNegativeStrip048Edge14true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 14 true := by decide +kernel
theorem shortNegativeStrip048Edge15false : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 15 false := by decide +kernel
theorem shortNegativeStrip048Edge15true : boundedNegativeEdgeCheck 350 shortNegativeStrip048T shortNegativeStrip048P 15 true := by decide +kernel
theorem shortNegativeStrip048Bound {t a : ℝ} (tl : ((129/100):ℝ)≤t) (tu : t≤((137/100):ℝ)) (al : ((1321126934018083/1649267441664000):ℝ)≤a) (au : a≤((1465666708120709/1649267441664000):ℝ)) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤(350:ℝ) := by
  have ts : shortNegativeStrip048T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have ps := primal_box_parameters_sound shortNegativeStrip048P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply bounded_negative_strip_of_grid (M:=350) ts ps (by linarith)
  intro k flag
  fin_cases k <;> cases flag
  · exact shortNegativeStrip048Edge0false
  · exact shortNegativeStrip048Edge0true
  · exact shortNegativeStrip048Edge1false
  · exact shortNegativeStrip048Edge1true
  · exact shortNegativeStrip048Edge2false
  · exact shortNegativeStrip048Edge2true
  · exact shortNegativeStrip048Edge3false
  · exact shortNegativeStrip048Edge3true
  · exact shortNegativeStrip048Edge4false
  · exact shortNegativeStrip048Edge4true
  · exact shortNegativeStrip048Edge5false
  · exact shortNegativeStrip048Edge5true
  · exact shortNegativeStrip048Edge6false
  · exact shortNegativeStrip048Edge6true
  · exact shortNegativeStrip048Edge7false
  · exact shortNegativeStrip048Edge7true
  · exact shortNegativeStrip048Edge8false
  · exact shortNegativeStrip048Edge8true
  · exact shortNegativeStrip048Edge9false
  · exact shortNegativeStrip048Edge9true
  · exact shortNegativeStrip048Edge10false
  · exact shortNegativeStrip048Edge10true
  · exact shortNegativeStrip048Edge11false
  · exact shortNegativeStrip048Edge11true
  · exact shortNegativeStrip048Edge12false
  · exact shortNegativeStrip048Edge12true
  · exact shortNegativeStrip048Edge13false
  · exact shortNegativeStrip048Edge13true
  · exact shortNegativeStrip048Edge14false
  · exact shortNegativeStrip048Edge14true
  · exact shortNegativeStrip048Edge15false
  · exact shortNegativeStrip048Edge15true

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeStrip048Bound
