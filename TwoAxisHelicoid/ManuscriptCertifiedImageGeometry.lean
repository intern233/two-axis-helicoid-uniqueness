import TwoAxisHelicoid.ManuscriptGraphRepresentedClasses
import TwoAxisHelicoid.CertifiedGlobalImmersion

namespace TwoAxisHelicoid
open Set Topology

/-- Geometric and numerical clauses of Theorem 1.1 in the manuscript C¹ class.
Every placement of each candidate is carried onto the actual embedded
period solution by an isometry and a strictly positive real scale. -/
def ManuscriptCertifiedImageGeometry : Prop :=
  let p := certifiedClosedParameters
  let E := EuclideanSpace ℝ (Fin 3)
  let Q := spatialSimilaritySetoid E
  let M := range certifiedTorusImmersion
  ManuscriptC1UniqueImageClass ∧
    (∃ (s : ManuscriptC1Surface) (U : E ≃ᵢ E), Quotient.mk Q (U '' s.1.image) = Quotient.mk Q M) ∧
    (∀ (s : ManuscriptC1Surface) (U : E ≃ᵢ E), ∃ (k : ℝ) (f : E ≃ᵢ E),
      0 < k ∧ (fun v => k • f v) '' (U '' s.1.image) = M) ∧
    IsClosedEmbedding certifiedTorusImmersion ∧
    certifiedPeriodPair.ω₁ = 2 ∧ certifiedPeriodPair.ω₂ = 1 + Complex.I*p.t ∧
    p.t ∈ Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
    p.a ∈ Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13)

theorem manuscript_certified_image_geometry_of_classification
    (unique : ∃! d : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))),
      ∃ s : OriginalHelicoidRepresentative, Quotient.mk _ s.image = d)
    (model : ∃ s : OriginalHelicoidRepresentative, Quotient.mk (spatialSimilaritySetoid _) s.image =
      Quotient.mk (spatialSimilaritySetoid _) (range certifiedTorusImmersion))
    (embedded : IsClosedEmbedding certifiedTorusImmersion)
    (parameters : let p := certifiedClosedParameters
      certifiedPeriodPair.ω₁ = 2 ∧ certifiedPeriodPair.ω₂ = 1 + Complex.I*p.t ∧
      p.t ∈ Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a ∈ Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13)) :
    ManuscriptCertifiedImageGeometry := by
  let E := EuclideanSpace ℝ (Fin 3)
  let Q := spatialSimilaritySetoid E
  have one := manuscript_C1_unique_class_of_original unique
  have hm := (manuscript_C1_represented_class_iff _).mp model
  refine ⟨one,hm,?_,embedded,parameters⟩
  obtain ⟨d,_,alone⟩ := one
  intro s U
  have a := alone (Quotient.mk Q (U '' s.1.image)) ⟨s,U,rfl⟩
  have b := alone (Quotient.mk Q (range certifiedTorusImmersion)) hm
  exact (spatial_similarity_iff_positive_scale_isometry _ _).mp
    (Quotient.exact (a.trans b.symm))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_certified_image_geometry_of_classification
