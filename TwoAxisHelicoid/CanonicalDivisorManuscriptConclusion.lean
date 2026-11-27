import TwoAxisHelicoid.GenusOneCanonicalDivisor
import TwoAxisHelicoid.PublishedMarkedEmbeddedExample
import TwoAxisHelicoid.ManuscriptSpinClassification
import TwoAxisHelicoid.MarkedHelicoidIntersectionTheorem

namespace TwoAxisHelicoid
open Complex Set Topology

/-- For the published differential end input, the two ordinary genus-one
canonical-divisor identities suffice in place of the uniformization of
all simply connected Riemann surfaces. -/
theorem original_manuscript_from_genus_one_riemann_roch (bbc : OneHandleGeometricExteriorPrinciple)
    (rr : GenusOneCanonicalDivisorFormula.{0}) (whw : PublishedMarkedEmbeddedHelicoidExample) :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let represents := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image=c
    (∃! c, represents c) ∧ represents (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : OriginalPositionallyAsymptoticHelicoid, HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
        HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid) ∧
      certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+I*p.t ∧
      p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) := by
  have norm (s : OriginalPositionallyAsymptoticHelicoid) : HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid :=
    original_pointed_model_from_exterior s.toOriginalSmoothHelicoid s.approaches (bbc _ s.not_simply_connected)
      (genus_one_period_uniformization_from_canonical_divisor rr s.modelTorus) marked_rhombic_helicoid_intersection
  obtain ⟨unique,model,embedding⟩ := positional_classification_of_pointed_models norm
    ((original_c1_representative_of_published_marked_example whw).map OriginalHelicoidRepresentative.toPositional)
  refine ⟨unique,model,embedding,fun s => ⟨norm s,original_pointed_gauss_divisor_of_normalization _ (norm s)⟩,
    rfl,rfl,?_,?_⟩
  · convert certifiedClosedParameters_bounds.1 using 1; norm_num [rootTLower,rootTUpper]
  · convert certifiedClosedParameters_bounds.2 using 1; norm_num [rootALower,rootAUpper]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_manuscript_from_genus_one_riemann_roch
