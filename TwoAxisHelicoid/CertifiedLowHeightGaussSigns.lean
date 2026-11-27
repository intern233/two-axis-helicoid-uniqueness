import TwoAxisHelicoid.LowHeightGaussFromCentralQuadrant
import TwoAxisHelicoid.CertifiedCentralLevelEmbedded

namespace TwoAxisHelicoid
open Complex Set

/-- At every low positive physical height two overlapping row ranges
have strictly signed Gauss components. The second range continues to
the puncture and includes its whole upper quarter. -/
theorem certified_low_height_gauss_signs :
    let p := certifiedClosedParameters
    let H := actualComplexHeight p.t p.a 1 p.height_pos
    let G := thetaGauss p.t p.a 1
    (∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioc (0:ℝ) (3/8) → 0<(H z).re → (G z).re<0) ∧
    ∀ z : ℂ, z.re∈Icc (0:ℝ) 1 → z.im∈Ioo (0:ℝ) p.t → 7/32≤z.im →
      (H z).re∈Ioc (0:ℝ) (1/4) → (G z).im<0 := by
  let p := certifiedClosedParameters
  have tb := Ioo_subset_Icc_self certifiedClosedParameters_bounds.1
  have ab := Ioo_subset_Icc_self certifiedClosedParameters_bounds.2
  have q := central_saddle_gauss_quadrant tb ab p.height_pos p.abscissa_mem p.vertical_closed
    certified_saddle_height_bracket.1 (by simpa only [div_one] using centralGaussRatioLeftCover)
    (by simpa only [div_one] using centralGaussRatioRightCover) (by simpa only [div_one] using centralGaussRatioBottomCover)
    centralGaussRatioTopCover (by simpa only [div_one] using centralGaussRatioLeftThirdCover)
  exact low_height_gauss_signs_of_central_quadrant q

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_low_height_gauss_signs
