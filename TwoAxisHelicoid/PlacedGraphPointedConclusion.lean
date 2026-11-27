import TwoAxisHelicoid.GraphPointedConclusionFromExistence

namespace TwoAxisHelicoid
open Set Topology

/-- The physical surface is a single C¹ normal graph at infinity in
the frame of its own asymptotic helicoid. Its position, axis and phase
are unrestricted in the original Euclidean space. -/
def PlacedPositionalHelicoid.HasGraphEnd (s : PlacedPositionalHelicoid) : Prop :=
  HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization s.pitch_ne ![0,0,0] ∘
    s.frame.homeo ∘ s.position)

abbrev PlacedGraphHelicoid := {s : PlacedPositionalHelicoid // s.HasGraphEnd}

noncomputable def PlacedGraphHelicoid.normalizedGraph (s : PlacedGraphHelicoid) :
    OriginalHelicoidRepresentative :=
  {s.1.normalized.toOriginalSmoothHelicoid with graphEnd := s.2}

theorem graph_placed_class_iff_original (c : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3)))) :
    (∃ s : PlacedGraphHelicoid, Quotient.mk _ s.1.image=c) ↔
    (∃ s : OriginalHelicoidRepresentative, Quotient.mk _ s.image=c) := by
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨s.normalizedGraph,(Quotient.sound s.1.image_equivalent_normalized).symm⟩
  · rintro ⟨s,rfl⟩
    have graph : s.toPositional.placed.HasGraphEnd := by
      change HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization s.axes.pitch_ne ![0,0,0] ∘
        HelicoidSpatialFrame.standard.homeo ∘ s.position)
      rw [show (HelicoidSpatialFrame.standard.homeo : (Fin 3 → ℝ) → (Fin 3 → ℝ))=id from
        funext HelicoidSpatialFrame.standard_apply,Function.id_comp]
      exact s.graphEnd
    exact ⟨⟨s.toPositional.placed,graph⟩,rfl⟩

def PlacedGraphTheoremOneOne : Prop :=
  let p := certifiedClosedParameters
  let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
  let rep := fun c : Quotient Q => ∃ s : PlacedGraphHelicoid, Quotient.mk Q s.1.image=c
  (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
    IsClosedEmbedding certifiedTorusImmersion ∧
    (∀ s : PlacedGraphHelicoid, HasPointedOriginalSpinBranchCap s.normalizedGraph.toPositional ∧
      HasCertifiedPointedNormalization s.normalizedGraph.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.normalizedGraph.toOriginalSmoothHelicoid) ∧
    certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+Complex.I*p.t ∧
    p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
    p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13)

theorem placed_pointed_graph_of_normalized (h : OriginalGraphTheoremOneOne) :
    PlacedGraphTheoremOneOne := by
  obtain ⟨⟨c,hc,unique⟩,rep,embedding,all,params⟩ := h
  exact ⟨⟨c,(graph_placed_class_iff_original c).mpr hc,fun u hu => unique u ((graph_placed_class_iff_original u).mp hu)⟩,
    (graph_placed_class_iff_original _).mpr rep,embedding,fun s => all s.normalizedGraph,params⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_placed_class_iff_original
#print axioms TwoAxisHelicoid.placed_pointed_graph_of_normalized
