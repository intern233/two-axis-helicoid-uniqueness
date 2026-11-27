import TwoAxisHelicoid.CertifiedGlobalImmersion
import TwoAxisHelicoid.ActualTorusProperness

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Spatial properness of the actual certified immersion into Euclidean
three-space. This theorem does not assert global embeddedness. -/
theorem certifiedTorusImmersion_isProperMap : IsProperMap certifiedTorusImmersion := by
  have hp := actualTorusImmersion_isProperMap
    certifiedClosedParameters.height_pos certifiedClosedParameters.abscissa_mem
    (by norm_num : (1 : ℝ) ≠ 0) certifiedClosedParameters.vertical_closed
    certifiedClosedParameters.horizontal_closed
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isProperMap.comp hp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certifiedTorusImmersion_isProperMap
