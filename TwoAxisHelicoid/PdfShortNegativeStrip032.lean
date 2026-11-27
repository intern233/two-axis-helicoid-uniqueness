import TwoAxisHelicoid.PdfBoundedNegativeStrip
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeStrip032T := Grid.ofRats (113/100) (121/100)
def shortNegativeStrip032P : PrimalThetaParameters := ⟨⟨⟨27008736320017587240873,34725969005087868206856,true⟩,⟨0,0,true⟩⟩, ⟨⟨1331274277187556343034383,1421785182078425081238576,true⟩,⟨0,0,true⟩⟩, ⟨(-1135403919261191534981277),(-954382109479522778055066),true⟩, ⟨3813246636908321942145837,4784599963273544810163060,true⟩⟩
theorem shortNegativeStrip032P_ok : shortNegativeStrip032P.encloses (primalThetaParameters shortNegativeStrip032T (Grid.ofRats (1156216322627161/1649267441664000) (1234825357146763/1649267441664000))) := by decide +kernel

theorem shortNegativeStrip032Edge0false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 0 false := by decide +kernel
theorem shortNegativeStrip032Edge0true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 0 true := by decide +kernel
theorem shortNegativeStrip032Edge1false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 1 false := by decide +kernel
theorem shortNegativeStrip032Edge1true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 1 true := by decide +kernel
theorem shortNegativeStrip032Edge2false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 2 false := by decide +kernel
theorem shortNegativeStrip032Edge2true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 2 true := by decide +kernel
theorem shortNegativeStrip032Edge3false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 3 false := by decide +kernel
theorem shortNegativeStrip032Edge3true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 3 true := by decide +kernel
theorem shortNegativeStrip032Edge4false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 4 false := by decide +kernel
theorem shortNegativeStrip032Edge4true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 4 true := by decide +kernel
theorem shortNegativeStrip032Edge5false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 5 false := by decide +kernel
theorem shortNegativeStrip032Edge5true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 5 true := by decide +kernel
theorem shortNegativeStrip032Edge6false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 6 false := by decide +kernel
theorem shortNegativeStrip032Edge6true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 6 true := by decide +kernel
theorem shortNegativeStrip032Edge7false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 7 false := by decide +kernel
theorem shortNegativeStrip032Edge7true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 7 true := by decide +kernel
theorem shortNegativeStrip032Edge8false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 8 false := by decide +kernel
theorem shortNegativeStrip032Edge8true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 8 true := by decide +kernel
theorem shortNegativeStrip032Edge9false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 9 false := by decide +kernel
theorem shortNegativeStrip032Edge9true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 9 true := by decide +kernel
theorem shortNegativeStrip032Edge10false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 10 false := by decide +kernel
theorem shortNegativeStrip032Edge10true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 10 true := by decide +kernel
theorem shortNegativeStrip032Edge11false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 11 false := by decide +kernel
theorem shortNegativeStrip032Edge11true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 11 true := by decide +kernel
theorem shortNegativeStrip032Edge12false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 12 false := by decide +kernel
theorem shortNegativeStrip032Edge12true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 12 true := by decide +kernel
theorem shortNegativeStrip032Edge13false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 13 false := by decide +kernel
theorem shortNegativeStrip032Edge13true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 13 true := by decide +kernel
theorem shortNegativeStrip032Edge14false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 14 false := by decide +kernel
theorem shortNegativeStrip032Edge14true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 14 true := by decide +kernel
theorem shortNegativeStrip032Edge15false : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 15 false := by decide +kernel
theorem shortNegativeStrip032Edge15true : boundedNegativeEdgeCheck 1440 shortNegativeStrip032T shortNegativeStrip032P 15 true := by decide +kernel
theorem shortNegativeStrip032Bound {t a : ℝ} (tl : ((113/100):ℝ)≤t) (tu : t≤((121/100):ℝ)) (al : ((1156216322627161/1649267441664000):ℝ)≤a) (au : a≤((1234825357146763/1649267441664000):ℝ)) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤(1440:ℝ) := by
  have ts : shortNegativeStrip032T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have ps := primal_box_parameters_sound shortNegativeStrip032P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply bounded_negative_strip_of_grid (M:=1440) ts ps (by linarith)
  intro k flag
  fin_cases k <;> cases flag
  · exact shortNegativeStrip032Edge0false
  · exact shortNegativeStrip032Edge0true
  · exact shortNegativeStrip032Edge1false
  · exact shortNegativeStrip032Edge1true
  · exact shortNegativeStrip032Edge2false
  · exact shortNegativeStrip032Edge2true
  · exact shortNegativeStrip032Edge3false
  · exact shortNegativeStrip032Edge3true
  · exact shortNegativeStrip032Edge4false
  · exact shortNegativeStrip032Edge4true
  · exact shortNegativeStrip032Edge5false
  · exact shortNegativeStrip032Edge5true
  · exact shortNegativeStrip032Edge6false
  · exact shortNegativeStrip032Edge6true
  · exact shortNegativeStrip032Edge7false
  · exact shortNegativeStrip032Edge7true
  · exact shortNegativeStrip032Edge8false
  · exact shortNegativeStrip032Edge8true
  · exact shortNegativeStrip032Edge9false
  · exact shortNegativeStrip032Edge9true
  · exact shortNegativeStrip032Edge10false
  · exact shortNegativeStrip032Edge10true
  · exact shortNegativeStrip032Edge11false
  · exact shortNegativeStrip032Edge11true
  · exact shortNegativeStrip032Edge12false
  · exact shortNegativeStrip032Edge12true
  · exact shortNegativeStrip032Edge13false
  · exact shortNegativeStrip032Edge13true
  · exact shortNegativeStrip032Edge14false
  · exact shortNegativeStrip032Edge14true
  · exact shortNegativeStrip032Edge15false
  · exact shortNegativeStrip032Edge15true

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeStrip032Bound
