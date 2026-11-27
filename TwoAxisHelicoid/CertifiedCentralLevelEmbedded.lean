import TwoAxisHelicoid.CentralLevelFromThetaEdges
import TwoAxisHelicoid.CentralGaussRatioLeftCover
import TwoAxisHelicoid.CentralGaussRatioRightCover
import TwoAxisHelicoid.CentralGaussRatioBottomCover
import TwoAxisHelicoid.CentralGaussRatioTopCover
import TwoAxisHelicoid.CentralGaussRatioLeftThirdCover
import TwoAxisHelicoid.CompactDoubleHeightGap

namespace TwoAxisHelicoid
open Set Topology

/-- The entire physical central level on the punctured torus has no
spatial double points, including the complete horizontal axis and both saddles. -/
theorem certified_central_height_level_injective :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    InjOn certifiedTorusImmersion {q | certifiedTorusImmersion q 2=X 1 2} :=
  certified_central_level_from_theta_edges
    (by simpa only [div_one] using centralGaussRatioLeftCover)
    (by simpa only [div_one] using centralGaussRatioRightCover)
    (by simpa only [div_one] using centralGaussRatioBottomCover)
    centralGaussRatioTopCover (by simpa only [div_one] using centralGaussRatioLeftThirdCover)

/-- The central level belongs to a whole closed, saturated, embedded
slab. Every double point of the complete immersion would have absolute
physical height strictly between two positive finite bounds. -/
theorem certified_embedded_central_slab :
    let p := certifiedClosedParameters
    let s := actualGlobalImmersion p.t p.a 1 p.height_pos 1 2
    ∃ ε R : ℝ, 0<ε ∧ ε<R ∧
      (∀ q∈immersionDoublePoints certifiedTorusImmersion, |certifiedTorusImmersion q.1 2-s|∈Ioo ε R) ∧
      IsClosedEmbedding (fun u : {u | |certifiedTorusImmersion u 2-s|≤ε} => certifiedTorusImmersion u.1) := by
  intro p s
  apply compact_double_height_gap certifiedTorusImmersion_isProperMap certified_compact_embedding_criterion.1
    (fun v => v 2) _ s certified_central_height_level_injective
  exact (EuclideanSpace.proj 2 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_central_height_level_injective
#print axioms TwoAxisHelicoid.certified_embedded_central_slab
