import TwoAxisHelicoid.PdfBoundedNegativeStrip
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeStrip024T := Grid.ofRats (21/20) (113/100)
def shortNegativeStrip024P : PrimalThetaParameters := ⟨⟨⟨34725969005019148729570,44648254144551759170335,true⟩,⟨0,0,true⟩⟩, ⟨⟨1257366770011990640305714,1336224028583220701682087,true⟩,⟨0,0,true⟩⟩, ⟨(-1283218933612322940439086),(-1125504416469931537167498),true⟩, ⟨4206235895064178811026554,5252489822370962206016596,true⟩⟩
theorem shortNegativeStrip024P_ok : shortNegativeStrip024P.encloses (primalThetaParameters shortNegativeStrip024T (Grid.ofRats (1092027396554317/1649267441664000) (232103039773043/329853488332800))) := by decide +kernel

theorem shortNegativeStrip024Edge0false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 0 false := by decide +kernel
theorem shortNegativeStrip024Edge0true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 0 true := by decide +kernel
theorem shortNegativeStrip024Edge1false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 1 false := by decide +kernel
theorem shortNegativeStrip024Edge1true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 1 true := by decide +kernel
theorem shortNegativeStrip024Edge2false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 2 false := by decide +kernel
theorem shortNegativeStrip024Edge2true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 2 true := by decide +kernel
theorem shortNegativeStrip024Edge3false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 3 false := by decide +kernel
theorem shortNegativeStrip024Edge3true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 3 true := by decide +kernel
theorem shortNegativeStrip024Edge4false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 4 false := by decide +kernel
theorem shortNegativeStrip024Edge4true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 4 true := by decide +kernel
theorem shortNegativeStrip024Edge5false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 5 false := by decide +kernel
theorem shortNegativeStrip024Edge5true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 5 true := by decide +kernel
theorem shortNegativeStrip024Edge6false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 6 false := by decide +kernel
theorem shortNegativeStrip024Edge6true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 6 true := by decide +kernel
theorem shortNegativeStrip024Edge7false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 7 false := by decide +kernel
theorem shortNegativeStrip024Edge7true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 7 true := by decide +kernel
theorem shortNegativeStrip024Edge8false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 8 false := by decide +kernel
theorem shortNegativeStrip024Edge8true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 8 true := by decide +kernel
theorem shortNegativeStrip024Edge9false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 9 false := by decide +kernel
theorem shortNegativeStrip024Edge9true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 9 true := by decide +kernel
theorem shortNegativeStrip024Edge10false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 10 false := by decide +kernel
theorem shortNegativeStrip024Edge10true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 10 true := by decide +kernel
theorem shortNegativeStrip024Edge11false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 11 false := by decide +kernel
theorem shortNegativeStrip024Edge11true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 11 true := by decide +kernel
theorem shortNegativeStrip024Edge12false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 12 false := by decide +kernel
theorem shortNegativeStrip024Edge12true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 12 true := by decide +kernel
theorem shortNegativeStrip024Edge13false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 13 false := by decide +kernel
theorem shortNegativeStrip024Edge13true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 13 true := by decide +kernel
theorem shortNegativeStrip024Edge14false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 14 false := by decide +kernel
theorem shortNegativeStrip024Edge14true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 14 true := by decide +kernel
theorem shortNegativeStrip024Edge15false : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 15 false := by decide +kernel
theorem shortNegativeStrip024Edge15true : boundedNegativeEdgeCheck 4190 shortNegativeStrip024T shortNegativeStrip024P 15 true := by decide +kernel
theorem shortNegativeStrip024Bound {t a : ℝ} (tl : ((21/20):ℝ)≤t) (tu : t≤((113/100):ℝ)) (al : ((1092027396554317/1649267441664000):ℝ)≤a) (au : a≤((232103039773043/329853488332800):ℝ)) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤(4190:ℝ) := by
  have ts : shortNegativeStrip024T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have ps := primal_box_parameters_sound shortNegativeStrip024P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply bounded_negative_strip_of_grid (M:=4190) ts ps (by linarith)
  intro k flag
  fin_cases k <;> cases flag
  · exact shortNegativeStrip024Edge0false
  · exact shortNegativeStrip024Edge0true
  · exact shortNegativeStrip024Edge1false
  · exact shortNegativeStrip024Edge1true
  · exact shortNegativeStrip024Edge2false
  · exact shortNegativeStrip024Edge2true
  · exact shortNegativeStrip024Edge3false
  · exact shortNegativeStrip024Edge3true
  · exact shortNegativeStrip024Edge4false
  · exact shortNegativeStrip024Edge4true
  · exact shortNegativeStrip024Edge5false
  · exact shortNegativeStrip024Edge5true
  · exact shortNegativeStrip024Edge6false
  · exact shortNegativeStrip024Edge6true
  · exact shortNegativeStrip024Edge7false
  · exact shortNegativeStrip024Edge7true
  · exact shortNegativeStrip024Edge8false
  · exact shortNegativeStrip024Edge8true
  · exact shortNegativeStrip024Edge9false
  · exact shortNegativeStrip024Edge9true
  · exact shortNegativeStrip024Edge10false
  · exact shortNegativeStrip024Edge10true
  · exact shortNegativeStrip024Edge11false
  · exact shortNegativeStrip024Edge11true
  · exact shortNegativeStrip024Edge12false
  · exact shortNegativeStrip024Edge12true
  · exact shortNegativeStrip024Edge13false
  · exact shortNegativeStrip024Edge13true
  · exact shortNegativeStrip024Edge14false
  · exact shortNegativeStrip024Edge14true
  · exact shortNegativeStrip024Edge15false
  · exact shortNegativeStrip024Edge15true

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeStrip024Bound
