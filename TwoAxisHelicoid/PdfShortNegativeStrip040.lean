import TwoAxisHelicoid.PdfBoundedNegativeStrip
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeStrip040T := Grid.ofRats (121/100) (129/100)
def shortNegativeStrip040P : PrimalThetaParameters := ⟨⟨⟨21006522164975248756275,27008736320086306718059,true⟩,⟨0,0,true⟩⟩, ⟨⟨1418851237116628090190338,1535316846770325745568755,true⟩,⟨0,0,true⟩⟩, ⟨(-960249999403048040668810),(-727318780095721449395431),true⟩, ⟨3415675413707800994212047,4432001039897365731604642,true⟩⟩
theorem shortNegativeStrip040P_ok : shortNegativeStrip040P.encloses (primalThetaParameters shortNegativeStrip040T (Grid.ofRats (1232277215781329/1649267441664000) (17779040017613/21990232555520))) := by decide +kernel

theorem shortNegativeStrip040Edge0false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 0 false := by decide +kernel
theorem shortNegativeStrip040Edge0true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 0 true := by decide +kernel
theorem shortNegativeStrip040Edge1false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 1 false := by decide +kernel
theorem shortNegativeStrip040Edge1true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 1 true := by decide +kernel
theorem shortNegativeStrip040Edge2false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 2 false := by decide +kernel
theorem shortNegativeStrip040Edge2true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 2 true := by decide +kernel
theorem shortNegativeStrip040Edge3false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 3 false := by decide +kernel
theorem shortNegativeStrip040Edge3true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 3 true := by decide +kernel
theorem shortNegativeStrip040Edge4false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 4 false := by decide +kernel
theorem shortNegativeStrip040Edge4true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 4 true := by decide +kernel
theorem shortNegativeStrip040Edge5false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 5 false := by decide +kernel
theorem shortNegativeStrip040Edge5true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 5 true := by decide +kernel
theorem shortNegativeStrip040Edge6false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 6 false := by decide +kernel
theorem shortNegativeStrip040Edge6true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 6 true := by decide +kernel
theorem shortNegativeStrip040Edge7false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 7 false := by decide +kernel
theorem shortNegativeStrip040Edge7true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 7 true := by decide +kernel
theorem shortNegativeStrip040Edge8false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 8 false := by decide +kernel
theorem shortNegativeStrip040Edge8true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 8 true := by decide +kernel
theorem shortNegativeStrip040Edge9false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 9 false := by decide +kernel
theorem shortNegativeStrip040Edge9true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 9 true := by decide +kernel
theorem shortNegativeStrip040Edge10false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 10 false := by decide +kernel
theorem shortNegativeStrip040Edge10true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 10 true := by decide +kernel
theorem shortNegativeStrip040Edge11false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 11 false := by decide +kernel
theorem shortNegativeStrip040Edge11true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 11 true := by decide +kernel
theorem shortNegativeStrip040Edge12false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 12 false := by decide +kernel
theorem shortNegativeStrip040Edge12true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 12 true := by decide +kernel
theorem shortNegativeStrip040Edge13false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 13 false := by decide +kernel
theorem shortNegativeStrip040Edge13true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 13 true := by decide +kernel
theorem shortNegativeStrip040Edge14false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 14 false := by decide +kernel
theorem shortNegativeStrip040Edge14true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 14 true := by decide +kernel
theorem shortNegativeStrip040Edge15false : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 15 false := by decide +kernel
theorem shortNegativeStrip040Edge15true : boundedNegativeEdgeCheck 600 shortNegativeStrip040T shortNegativeStrip040P 15 true := by decide +kernel
theorem shortNegativeStrip040Bound {t a : ℝ} (tl : ((121/100):ℝ)≤t) (tu : t≤((129/100):ℝ)) (al : ((1232277215781329/1649267441664000):ℝ)≤a) (au : a≤((17779040017613/21990232555520):ℝ)) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤(600:ℝ) := by
  have ts : shortNegativeStrip040T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have ps := primal_box_parameters_sound shortNegativeStrip040P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply bounded_negative_strip_of_grid (M:=600) ts ps (by linarith)
  intro k flag
  fin_cases k <;> cases flag
  · exact shortNegativeStrip040Edge0false
  · exact shortNegativeStrip040Edge0true
  · exact shortNegativeStrip040Edge1false
  · exact shortNegativeStrip040Edge1true
  · exact shortNegativeStrip040Edge2false
  · exact shortNegativeStrip040Edge2true
  · exact shortNegativeStrip040Edge3false
  · exact shortNegativeStrip040Edge3true
  · exact shortNegativeStrip040Edge4false
  · exact shortNegativeStrip040Edge4true
  · exact shortNegativeStrip040Edge5false
  · exact shortNegativeStrip040Edge5true
  · exact shortNegativeStrip040Edge6false
  · exact shortNegativeStrip040Edge6true
  · exact shortNegativeStrip040Edge7false
  · exact shortNegativeStrip040Edge7true
  · exact shortNegativeStrip040Edge8false
  · exact shortNegativeStrip040Edge8true
  · exact shortNegativeStrip040Edge9false
  · exact shortNegativeStrip040Edge9true
  · exact shortNegativeStrip040Edge10false
  · exact shortNegativeStrip040Edge10true
  · exact shortNegativeStrip040Edge11false
  · exact shortNegativeStrip040Edge11true
  · exact shortNegativeStrip040Edge12false
  · exact shortNegativeStrip040Edge12true
  · exact shortNegativeStrip040Edge13false
  · exact shortNegativeStrip040Edge13true
  · exact shortNegativeStrip040Edge14false
  · exact shortNegativeStrip040Edge14true
  · exact shortNegativeStrip040Edge15false
  · exact shortNegativeStrip040Edge15true

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeStrip040Bound
