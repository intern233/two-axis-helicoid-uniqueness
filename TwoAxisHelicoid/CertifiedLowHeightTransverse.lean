import TwoAxisHelicoid.LowHeightTransverseFromCentral
import TwoAxisHelicoid.CertifiedCentralLevelEmbedded

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- Between the central plane and relative physical height one quarter
the open first-quarter arc stays strictly on one transverse side of
the marked vertical axis. -/
theorem certified_low_height_transverse_positive :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∀ z : ℂ, z.re∈Ioo (0:ℝ) 1 → z.im∈Ioo (0:ℝ) p.t →
      X z 2-X 1 2∈Ioc (0:ℝ) (1/4) → X 1 1<X z 1 :=
  low_height_transverse_of_central_injectivity certified_central_height_level_injective

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_low_height_transverse_positive
