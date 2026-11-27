import TwoAxisHelicoid.MinimalHelicoidHeightGraphUpgrade
import TwoAxisHelicoid.CertifiedOriginalMarkedConclusion

namespace TwoAxisHelicoid
open Set Topology

def PlacedPositionalHelicoid.HasHeightGraphEnd (s : PlacedPositionalHelicoid) : Prop :=
  HasHelicoidHeightEnd (coordinateToTube ∘ axisSpatialNormalization s.pitch_ne ![0,0,0] ∘
    s.frame.homeo ∘ s.position)

theorem PlacedPositionalHelicoid.height_graph_iff_C1 (s : PlacedPositionalHelicoid) :
    s.HasHeightGraphEnd ↔ s.HasGraphEnd :=
  original_helicoid_graph_height_iff_C1 s.normalized.toOriginalSmoothHelicoid

/-- Theorem 1.1 with only decay of the height of a single smooth normal
graph assumed. The free spatial placement, actual closed embedding and
common compactification, cap and Gauss marking are retained. -/
theorem placed_height_graph_one_one_same_marking :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : PlacedPositionalHelicoid, s.HasHeightGraphEnd ∧ Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : PlacedPositionalHelicoid, s.HasHeightGraphEnd → HasCertifiedSpinCapGaussMarking s.normalized) ∧
      certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+Complex.I*p.t ∧
      p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) := by
  obtain ⟨⟨⟨c,rep,only⟩,repModel,emb,_,params⟩,joint⟩ := placed_graph_one_one_same_marking
  have equiv (b : Quotient (spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3)))) :
      (∃ s : PlacedGraphHelicoid, Quotient.mk _ s.1.image=b) ↔
      (∃ s : PlacedPositionalHelicoid, s.HasHeightGraphEnd ∧ Quotient.mk _ s.image=b) := by
    constructor
    · rintro ⟨s,eq⟩
      exact ⟨s.1,s.1.height_graph_iff_C1.mpr s.2,eq⟩
    · rintro ⟨s,h,eq⟩
      exact ⟨⟨s,s.height_graph_iff_C1.mp h⟩,eq⟩
  exact ⟨⟨c,(equiv _).mp rep,fun b h => only b ((equiv _).mpr h)⟩,(equiv _).mp repModel,emb,
    fun s h => joint ⟨s,s.height_graph_iff_C1.mp h⟩,params⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.placed_height_graph_one_one_same_marking
