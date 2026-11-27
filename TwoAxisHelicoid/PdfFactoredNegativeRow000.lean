import TwoAxisHelicoid.PdfFactoredNegativeRow000Samples
import TwoAxisHelicoid.PdfFirstNegativeStrip

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factoredNegativeR000Q00Bound {t a : ℝ} (tl : ((9/10):ℝ)≤t) (tu : t≤((361/400):ℝ)) (al : ((996784061054281/1649267441664000):ℝ)≤a) (au : a≤((998394673790281/1649267441664000):ℝ)) : (((-1463110353651696498115893616266867/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-287277687557085476657562098683507/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : factoredNegativeR000Q00T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (996784061054281/1649267441664000) (998394673790281/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound factoredNegativeR000Q00P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredNegativeR000Q00F_ok n) ts asb
  exact factored_negative_24_samples ps fs factoredNodes24Sound (by linarith) (by linarith) (first_negative_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredNegativeR000Q00L factoredNegativeR000Q00U (-1463110353651696498115893616266867/2596148429267413814265248164610048) (-287277687557085476657562098683507/2596148429267413814265248164610048) factoredNegativeR000Q00Samples (by decide +kernel)



theorem factoredNegativeR000Q01Bound {t a : ℝ} (tl : ((9/10):ℝ)≤t) (tu : t≤((361/400):ℝ)) (al : ((998394673790281/1649267441664000):ℝ)≤a) (au : a≤((1000005286526281/1649267441664000):ℝ)) : (((-1463110353651696498115893616266867/2596148429267413814265248164610048):ℚ):ℝ)≤thetaHorizontalPeriod t a ∧ thetaHorizontalPeriod t a≤(((-287277687557085476657562098683507/2596148429267413814265248164610048):ℚ):ℝ) := by
  have ts : factoredNegativeR000Q01T.Contains t := Grid.contains_rats (by push_cast; exact tl) (by push_cast; exact tu)
  have asb : (Grid.ofRats (998394673790281/1649267441664000) (1000005286526281/1649267441664000)).Contains a := Grid.contains_rats (by push_cast; exact al) (by push_cast; exact au)
  have ps := primal_box_parameters_sound factoredNegativeR000Q01P_ok (t:=t) (a:=a) (by push_cast; exact tl) (by push_cast; exact tu) (by push_cast; exact al) (by push_cast; exact au) (by linarith)
  have fs (n : Fin 6) := FactoredFrequency.box_sound (factoredNegativeR000Q01F_ok n) ts asb
  exact factored_negative_24_samples ps fs factoredNodes24Sound (by linarith) (by linarith) (first_negative_strip_edges (by linarith) (by linarith) (by linarith) (by linarith)) factoredNegativeR000Q01L factoredNegativeR000Q01U (-1463110353651696498115893616266867/2596148429267413814265248164610048) (-287277687557085476657562098683507/2596148429267413814265248164610048) factoredNegativeR000Q01Samples (by decide +kernel)

theorem factored_original_negative_000 {t a : ℝ} (tb : RealMem negative_000.t t) (ab : RealMem negative_000.a a) : RealMem negative_000.hReal (thetaHorizontalPeriod t a) := by
  have tB : t∈Icc ((9/10):ℝ) ((361/400):ℝ) := by simpa [negative_000,RealMem] using tb
  obtain ⟨ti,tl,tu⟩ := closed_uniform_cell (N:=1) (by decide) (by norm_num : ((9/10):ℝ)<((361/400):ℝ)) tB
  have aB : a∈Icc ((996784061054281/1649267441664000):ℝ) ((1000005286526281/1649267441664000):ℝ) := by simpa [negative_000,RealMem] using ab
  obtain ⟨ai,al,au⟩ := closed_uniform_cell (N:=2) (by decide) (by norm_num : ((996784061054281/1649267441664000):ℝ)<((1000005286526281/1649267441664000):ℝ)) aB
  fin_cases ti
  fin_cases ai
  · norm_num at tl tu al au
    have v := @factoredNegativeR000Q00Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_000,RealMem] using v
  · norm_num at tl tu al au
    have v := @factoredNegativeR000Q01Bound t a (by linarith) (by linarith) (by linarith) (by linarith)
    simpa [negative_000,RealMem] using v

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_original_negative_000
