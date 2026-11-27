import TwoAxisHelicoid.PublishedGeometricClassification
import TwoAxisHelicoid.MarkedHelicoidIntersectionTheorem

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology Manifold ContDiff

/-- TwoAxisHelicoid, Theorem 1.1 from the published compactification, classical
uniformization and existence of one embedded surface. The exact
intersection and the integer-branch exclusion in the compact core
follow internally from the geometric hypotheses. -/
theorem theorem_1_1_from_end_uniformization_existence (bbc : PublishedOneHandleEndTheorem)
    (poincare : SimplyConnectedNoncompactUniformization.{0}) (existence : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let represents := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image=c
    (∃! c, represents c) ∧ represents (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : OriginalPositionallyAsymptoticHelicoid,
        HasHelicoidalC1End s.position ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid) ∧
      certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+I*p.t ∧
      p.t∈Ioo (866227694384/10^12 : ℝ) (866227694385/10^12) ∧
      p.a∈Ioo (5936860965140/10^13 : ℝ) (5936860965150/10^13) ∧
      GaussZeroPoleData p.t p.a p.height_pos (immersionGaussMap (actualGlobalImmersion p.t p.a 1 p.height_pos)) := by
  let p := certifiedClosedParameters
  have normalize (s : OriginalPositionallyAsymptoticHelicoid) := published_end_pointed_normalization s bbc
    (compact_genus_one_uniformization_of_classical poincare s.modelTorus) marked_rhombic_helicoid_intersection
  obtain ⟨hc,hr,he⟩ := positional_classification_of_pointed_models (fun s => (normalize s).2) existence
  refine ⟨hc,hr,he,normalize,rfl,rfl,?_,?_,
    closed_immersion_gauss_divisor p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed⟩
  · convert certifiedClosedParameters_bounds.1 using 1; norm_num [rootTLower,rootTUpper]
  · convert certifiedClosedParameters_bounds.2 using 1; norm_num [rootALower,rootAUpper]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.theorem_1_1_from_end_uniformization_existence
