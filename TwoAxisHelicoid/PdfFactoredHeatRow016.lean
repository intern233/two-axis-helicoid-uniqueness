import TwoAxisHelicoid.PdfFactoredHeatRow016Samples
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR016Q00Bound {t a : ℝ} (tl : ((433/500):ℝ)≤t) (tu : t≤((867/1000):ℝ)) (al : ((326162273349547/549755813888000):ℝ)≤a) (au : a≤((326699144261547/549755813888000):ℝ)) : reportedHeatPeriod t a≤(((-339658895985169048320981169680393/40564819207303340847894502572032):ℚ):ℝ) := by
  have ts : factoredHeatR016Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (326162273349547/549755813888000) (326699144261547/549755813888000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR016Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR016Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR016Q00U (-339658895985169048320981169680393/40564819207303340847894502572032) factoredHeatR016Q00Samples (by decide +kernel)

theorem factored_original_heat_016 {t a : ℝ} (tb : RealMem derivative_016.t t) (ab : RealMem derivative_016.a a) : reportedHeatPeriod t a≤(derivative_016.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((433/500):ℝ) ((867/1000):ℝ) := by simpa [derivative_016,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((433/500):ℝ)<((867/1000):ℝ)) tB
  have aB : a∈Icc ((326162273349547/549755813888000):ℝ) ((326699144261547/549755813888000):ℝ) := by simpa [derivative_016,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((326162273349547/549755813888000):ℝ)<((326699144261547/549755813888000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR016Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_016] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_016
