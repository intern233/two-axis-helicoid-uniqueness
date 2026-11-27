import TwoAxisHelicoid.CertifiedLowHeightGaussSigns
import TwoAxisHelicoid.CertifiedLowHeightPositions
import TwoAxisHelicoid.CertifiedLowHeightTransverse
import TwoAxisHelicoid.CertifiedEmbeddingFromLowWindows

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Every low positive horizontal section of the actual torus
immersion is embedded, including both copies of the quarter arc and
the intersection with the vertical axis. -/
theorem certified_low_positive_level_injective :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    ∀ h∈Ioc (0:ℝ) (1/4), InjOn certifiedTorusImmersion {q | certifiedTorusImmersion q 2=X 1 2+h} :=
  low_positive_level_injective_of_windows certified_low_height_transverse_positive certified_low_height_gauss_signs
    certified_low_height_window_positions

/-- Unconditional global closed embedding of the certified period
solution. Positive heights are covered by the two explicit ranges,
negative heights by the marked half-turn, and the central fiber
includes both saddles and the infinite real axis. -/
theorem certified_global_closed_embedding : IsClosedEmbedding certifiedTorusImmersion :=
  global_embedding_of_low_positive_levels certified_central_height_level_injective certified_low_positive_level_injective

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_low_positive_level_injective
#print axioms TwoAxisHelicoid.certified_global_closed_embedding
