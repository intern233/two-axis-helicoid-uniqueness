import TwoAxisHelicoid.PdfBoundedNegativeStrip
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def shortNegativeStrip016T := Grid.ofRats (97/100) (21/20)
def shortNegativeStrip016P : PrimalThetaParameters := ⟨⟨⟨44648254144483039692930,57405643536239648341027,true⟩,⟨0,0,true⟩⟩, ⟨⟨1193556254993271636869535,1263721842585269732597367,true⟩,⟨0,0,true⟩⟩, ⟨(-1410839963649760947311850),(-1270508788465833475336478),true⟩, ⟨4633374601175504311818166,5808172819126054646785732,true⟩⟩
theorem shortNegativeStrip016P_ok : shortNegativeStrip016P.encloses (primalThetaParameters shortNegativeStrip016T (Grid.ofRats (345535914385319/549755813888000) (1097546799104593/1649267441664000))) := by decide +kernel

theorem shortNegativeStrip016Edge0false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 0 false := by decide +kernel
theorem shortNegativeStrip016Edge0true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 0 true := by decide +kernel
theorem shortNegativeStrip016Edge1false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 1 false := by decide +kernel
theorem shortNegativeStrip016Edge1true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 1 true := by decide +kernel
theorem shortNegativeStrip016Edge2false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 2 false := by decide +kernel
theorem shortNegativeStrip016Edge2true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 2 true := by decide +kernel
theorem shortNegativeStrip016Edge3false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 3 false := by decide +kernel
theorem shortNegativeStrip016Edge3true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 3 true := by decide +kernel
theorem shortNegativeStrip016Edge4false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 4 false := by decide +kernel
theorem shortNegativeStrip016Edge4true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 4 true := by decide +kernel
theorem shortNegativeStrip016Edge5false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 5 false := by decide +kernel
theorem shortNegativeStrip016Edge5true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 5 true := by decide +kernel
theorem shortNegativeStrip016Edge6false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 6 false := by decide +kernel
theorem shortNegativeStrip016Edge6true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 6 true := by decide +kernel
theorem shortNegativeStrip016Edge7false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 7 false := by decide +kernel
theorem shortNegativeStrip016Edge7true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 7 true := by decide +kernel
theorem shortNegativeStrip016Edge8false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 8 false := by decide +kernel
theorem shortNegativeStrip016Edge8true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 8 true := by decide +kernel
theorem shortNegativeStrip016Edge9false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 9 false := by decide +kernel
theorem shortNegativeStrip016Edge9true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 9 true := by decide +kernel
theorem shortNegativeStrip016Edge10false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 10 false := by decide +kernel
theorem shortNegativeStrip016Edge10true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 10 true := by decide +kernel
theorem shortNegativeStrip016Edge11false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 11 false := by decide +kernel
theorem shortNegativeStrip016Edge11true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 11 true := by decide +kernel
theorem shortNegativeStrip016Edge12false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 12 false := by decide +kernel
theorem shortNegativeStrip016Edge12true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 12 true := by decide +kernel
theorem shortNegativeStrip016Edge13false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 13 false := by decide +kernel
theorem shortNegativeStrip016Edge13true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 13 true := by decide +kernel
theorem shortNegativeStrip016Edge14false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 14 false := by decide +kernel
theorem shortNegativeStrip016Edge14true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 14 true := by decide +kernel
theorem shortNegativeStrip016Edge15false : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 15 false := by decide +kernel
theorem shortNegativeStrip016Edge15true : boundedNegativeEdgeCheck 16770 shortNegativeStrip016T shortNegativeStrip016P 15 true := by decide +kernel
theorem shortNegativeStrip016Bound {t a : ℝ} (tl : ((97/100):ℝ)≤t) (tu : t≤((21/20):ℝ)) (al : ((345535914385319/549755813888000):ℝ)≤a) (au : a≤((1097546799104593/1649267441664000):ℝ)) :
    ∀ z : ℂ, z.re∈Icc (-1:ℝ) 0 → |z.im|=3/16 → ‖thetaA t a (z+Complex.I*((t/2:ℝ):ℂ))‖≤(16770:ℝ) := by
  have ts : shortNegativeStrip016T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have ps := primal_box_parameters_sound shortNegativeStrip016P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  apply bounded_negative_strip_of_grid (M:=16770) ts ps (by linarith)
  intro k flag
  fin_cases k <;> cases flag
  · exact shortNegativeStrip016Edge0false
  · exact shortNegativeStrip016Edge0true
  · exact shortNegativeStrip016Edge1false
  · exact shortNegativeStrip016Edge1true
  · exact shortNegativeStrip016Edge2false
  · exact shortNegativeStrip016Edge2true
  · exact shortNegativeStrip016Edge3false
  · exact shortNegativeStrip016Edge3true
  · exact shortNegativeStrip016Edge4false
  · exact shortNegativeStrip016Edge4true
  · exact shortNegativeStrip016Edge5false
  · exact shortNegativeStrip016Edge5true
  · exact shortNegativeStrip016Edge6false
  · exact shortNegativeStrip016Edge6true
  · exact shortNegativeStrip016Edge7false
  · exact shortNegativeStrip016Edge7true
  · exact shortNegativeStrip016Edge8false
  · exact shortNegativeStrip016Edge8true
  · exact shortNegativeStrip016Edge9false
  · exact shortNegativeStrip016Edge9true
  · exact shortNegativeStrip016Edge10false
  · exact shortNegativeStrip016Edge10true
  · exact shortNegativeStrip016Edge11false
  · exact shortNegativeStrip016Edge11true
  · exact shortNegativeStrip016Edge12false
  · exact shortNegativeStrip016Edge12true
  · exact shortNegativeStrip016Edge13false
  · exact shortNegativeStrip016Edge13true
  · exact shortNegativeStrip016Edge14false
  · exact shortNegativeStrip016Edge14true
  · exact shortNegativeStrip016Edge15false
  · exact shortNegativeStrip016Edge15true

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.shortNegativeStrip016Bound
