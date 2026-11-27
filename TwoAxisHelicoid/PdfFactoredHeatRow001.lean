import TwoAxisHelicoid.PdfFactoredHeatRow001Samples
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR001Q00Bound {t a : ℝ} (tl : ((851/1000):ℝ)≤t) (tu : t≤((213/250):ℝ)) (al : ((38824337804321/65970697666560):ℝ)≤a) (au : a≤((38888762313761/65970697666560):ℝ)) : reportedHeatPeriod t a≤(((-1352759609778169679828202085311837/162259276829213363391578010288128):ℚ):ℝ) := by
  have ts : factoredHeatR001Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (38824337804321/65970697666560) (38888762313761/65970697666560)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR001Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR001Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR001Q00U (-1352759609778169679828202085311837/162259276829213363391578010288128) factoredHeatR001Q00Samples (by decide +kernel)

theorem factored_original_heat_001 {t a : ℝ} (tb : RealMem derivative_001.t t) (ab : RealMem derivative_001.a a) : reportedHeatPeriod t a≤(derivative_001.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((851/1000):ℝ) ((213/250):ℝ) := by simpa [derivative_001,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((851/1000):ℝ)<((213/250):ℝ)) tB
  have aB : a∈Icc ((38824337804321/65970697666560):ℝ) ((38888762313761/65970697666560):ℝ) := by simpa [derivative_001,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((38824337804321/65970697666560):ℝ)<((38888762313761/65970697666560):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR001Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_001] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_001
