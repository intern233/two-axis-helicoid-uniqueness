import TwoAxisHelicoid.PdfFactoredNegativeRow001Samples
import TwoAxisHelicoid.PdfFirstNegativeStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredNegativeR001Q00Bound {t a : ℝ} (tl : ((361/400):ℝ)≤t) (tu : t≤((181/200):ℝ)) (al : ((998204904599263/1649267441664000):ℝ)≤a) (au : a≤((999815517335263/1649267441664000):ℝ)) : (((-379560124196352653854308821037687/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1407012846859325259725840254445423/10384593717069655257060992658440192):ℚ):ℝ) := by
  have ts : factoredNegativeR001Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (998204904599263/1649267441664000) (999815517335263/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound factoredNegativeR001Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredNegativeR001Q00F_ok n) ts asb
  exact factored_negative_24_samples ps fs factoredNodes24Sound (by linarith) (by linarith) (first_negative_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredNegativeR001Q00L factoredNegativeR001Q00U (-379560124196352653854308821037687/649037107316853453566312041152512) (-1407012846859325259725840254445423/10384593717069655257060992658440192) factoredNegativeR001Q00Samples (by decide +kernel)

theorem factoredNegativeR001Q01Bound {t a : ℝ} (tl : ((361/400):ℝ)≤t) (tu : t≤((181/200):ℝ)) (al : ((999815517335263/1649267441664000):ℝ)≤a) (au : a≤((1001426130071263/1649267441664000):ℝ)) : (((-379560124196352653854308821037687/649037107316853453566312041152512):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-1407012846859325259725840254445423/10384593717069655257060992658440192):ℚ):ℝ) := by
  have ts : factoredNegativeR001Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (999815517335263/1649267441664000) (1001426130071263/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound factoredNegativeR001Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredNegativeR001Q01F_ok n) ts asb
  exact factored_negative_24_samples ps fs factoredNodes24Sound (by linarith) (by linarith) (first_negative_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredNegativeR001Q01L factoredNegativeR001Q01U (-379560124196352653854308821037687/649037107316853453566312041152512) (-1407012846859325259725840254445423/10384593717069655257060992658440192) factoredNegativeR001Q01Samples (by decide +kernel)

theorem factored_original_negative_001 {t a : ℝ} (tb : RealMem negative_001.t t) (ab : RealMem negative_001.a a) : RealMem negative_001.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((361/400):ℝ) ((181/200):ℝ) := by simpa [negative_001,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((361/400):ℝ)<((181/200):ℝ)) tB
  have aB : a∈Icc ((998204904599263/1649267441664000):ℝ) ((1001426130071263/1649267441664000):ℝ) := by simpa [negative_001,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((998204904599263/1649267441664000):ℝ)<((1001426130071263/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredNegativeR001Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_001,RealMem] using v
  · norm_num at tl tu al au
    have v := @factoredNegativeR001Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_001,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_negative_001
