import TwoAxisHelicoid.ManuscriptC1GraphClassification

namespace TwoAxisHelicoid
open Set Topology


/-- The full Section 2 classification of normalized candidates under arbitrary Euclidean placements. -/
def ManuscriptC1TheoremOneOne : Prop :=
    let p := certifiedClosedParameters
    let E := EuclideanSpace ℝ (Fin 3)
    let Q := spatialSimilaritySetoid E
    let rep := fun c : Quotient Q => ∃ (s : ManuscriptC1Surface) (U : E ≃ᵢ E),
      Quotient.mk Q (U '' s.1.image) = c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : ManuscriptC1Surface, HasCertifiedSpinCapGaussMarking s.graphRepresentative.toPositional) ∧
      certifiedPeriodPair.ω₁ = 2 ∧ certifiedPeriodPair.ω₂ = 1 + Complex.I*p.t ∧
      p.t ∈ Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a ∈ Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13)

theorem manuscript_theorem_one_one : ManuscriptC1TheoremOneOne :=
  manuscript_C1_graph_one_one_same_marking

/-- The same conclusions when the position map and the axes are presented in the physical frame. -/
def PlacedManuscriptC1TheoremOneOne : Prop :=
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : PlacedPositionalHelicoid, s.HasManuscriptC1Graph ∧
      Quotient.mk Q s.image = c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : PlacedPositionalHelicoid, s.HasManuscriptC1Graph → HasCertifiedSpinCapGaussMarking s.normalized) ∧
      certifiedPeriodPair.ω₁ = 2 ∧ certifiedPeriodPair.ω₂ = 1 + Complex.I*p.t ∧
      p.t ∈ Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a ∈ Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13)

theorem placed_manuscript_theorem_one_one : PlacedManuscriptC1TheoremOneOne :=
  placed_manuscript_C1_graph_one_one_same_marking

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_theorem_one_one
#print axioms TwoAxisHelicoid.placed_manuscript_theorem_one_one
