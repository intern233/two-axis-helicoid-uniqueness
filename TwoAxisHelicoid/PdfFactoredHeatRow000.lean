import TwoAxisHelicoid.PdfFactoredHeatRow000Samples
import TwoAxisHelicoid.PdfHeatStripAll

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredHeatR000Q00Bound {t a : ℝ} (tl : ((17/20):ℝ)≤t) (tu : t≤((851/1000):ℝ)) (al : ((970090990727617/1649267441664000):ℝ)≤a) (au : a≤((971701603463617/1649267441664000):ℝ)) : reportedHeatPeriod t a≤(((-2691080614851898377952641248282051/324518553658426726783156020576256):ℚ):ℝ) := by
  have ts : factoredHeatR000Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (970090990727617/1649267441664000) (971701603463617/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := heat_box_parameters_sound factoredHeatR000Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredHeatR000Q00F_ok n) ts asb
  exact factored_heat_32_samples ps fs factoredNodes32Sound (by linarith) (by linarith) (original_heat_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredHeatR000Q00U (-2691080614851898377952641248282051/324518553658426726783156020576256) factoredHeatR000Q00Samples (by decide +kernel)

theorem factored_original_heat_000 {t a : ℝ} (tb : RealMem derivative_000.t t) (ab : RealMem derivative_000.a a) : reportedHeatPeriod t a≤(derivative_000.hPrimeUpper:ℝ) := by
  have tB : t∈Icc ((17/20):ℝ) ((851/1000):ℝ) := by simpa [derivative_000,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((17/20):ℝ)<((851/1000):ℝ)) tB
  have aB : a∈Icc ((970090990727617/1649267441664000):ℝ) ((971701603463617/1649267441664000):ℝ) := by simpa [derivative_000,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((970090990727617/1649267441664000):ℝ)<((971701603463617/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredHeatR000Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [derivative_000] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_heat_000
