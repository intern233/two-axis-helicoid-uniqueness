import TwoAxisHelicoid.ManuscriptGraphRepresentedClasses
import TwoAxisHelicoid.GraphTheoremByContactAndSpin
import TwoAxisHelicoid.CertifiedOriginalMarkedConclusion

namespace TwoAxisHelicoid
open Set Topology

/-- Existence and uniqueness of the physical image class from Section 2. -/
theorem original_manuscript_C1_unique_class : ManuscriptC1UniqueImageClass :=
  manuscript_C1_unique_class_of_original original_graph_one_one_by_contact_and_spin.1

/-- Theorem 1.1 for all isometric placements of smooth double-axis surfaces
with the single C¹ graph of Section 2 on arbitrary compact complements.
Each surface has a common spin, cap and Gauss marking and the certified
representative is globally embedded. -/
theorem manuscript_C1_graph_one_one_same_marking :
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
      p.a ∈ Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) := by
  intro p E Q rep
  obtain ⟨unique,model,embedding,_,periods⟩ := original_graph_one_one_by_contact_and_spin
  have represented_iff (d : Quotient Q) :
      (∃ s : OriginalHelicoidRepresentative, Quotient.mk Q s.image = d) ↔ rep d :=
    manuscript_C1_represented_class_iff d
  exact ⟨manuscript_C1_unique_class_of_original unique,
    (represented_iff _).mp model,embedding,
    fun s => original_graph_certified_spin_cap_gauss_marking s.graphRepresentative,periods⟩

def PlacedPositionalHelicoid.HasManuscriptC1Graph (s : PlacedPositionalHelicoid) : Prop :=
  HasCompactComplementC1Graph (coordinateToTube ∘ axisSpatialNormalization s.pitch_ne ![0,0,0] ∘
    s.frame.homeo ∘ s.position)

theorem PlacedPositionalHelicoid.manuscript_graph_iff_C1 (s : PlacedPositionalHelicoid) :
    s.HasManuscriptC1Graph ↔ s.HasGraphEnd :=
  original_compact_complement_C1_graph_iff s.normalized.toOriginalSmoothHelicoid

/-- The same result for candidates specified directly by a physical
position map and a reference frame in that physical Euclidean space. -/
theorem placed_manuscript_C1_graph_one_one_same_marking :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : PlacedPositionalHelicoid, s.HasManuscriptC1Graph ∧
      Quotient.mk Q s.image = c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : PlacedPositionalHelicoid, s.HasManuscriptC1Graph → HasCertifiedSpinCapGaussMarking s.normalized) ∧
      certifiedPeriodPair.ω₁ = 2 ∧ certifiedPeriodPair.ω₂ = 1 + Complex.I*p.t ∧
      p.t ∈ Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a ∈ Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) := by
  obtain ⟨⟨⟨c,represented,only⟩,model,embedding,_,periods⟩,joint⟩ := placed_graph_one_one_same_marking
  have represented_iff (d : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3)))) :
      (∃ s : PlacedGraphHelicoid, Quotient.mk _ s.1.image = d) ↔
      (∃ s : PlacedPositionalHelicoid, s.HasManuscriptC1Graph ∧ Quotient.mk _ s.image = d) := by
    constructor
    · rintro ⟨s,eq⟩
      exact ⟨s.1,s.1.manuscript_graph_iff_C1.mpr s.2,eq⟩
    · rintro ⟨s,h,eq⟩
      exact ⟨⟨s,s.manuscript_graph_iff_C1.mp h⟩,eq⟩
  exact ⟨⟨c,(represented_iff _).mp represented,fun d hd => only d ((represented_iff _).mpr hd)⟩,
    (represented_iff _).mp model,embedding,fun s h => joint ⟨s,s.manuscript_graph_iff_C1.mp h⟩,periods⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_manuscript_C1_unique_class
#print axioms TwoAxisHelicoid.manuscript_C1_graph_one_one_same_marking
#print axioms TwoAxisHelicoid.placed_manuscript_C1_graph_one_one_same_marking
