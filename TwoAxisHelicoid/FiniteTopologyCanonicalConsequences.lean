import TwoAxisHelicoid.CanonicalDivisorManuscriptConclusion
import TwoAxisHelicoid.FiniteTopologyEndConsequences
import TwoAxisHelicoid.OriginalGraphAppendices

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- The differential end theorem and the genus-one form identities give
the appendix B parameter exclusion and finiteness directly on the
original weakly asymptotic surfaces. This proof uses the analytic
endpoint estimates and does not use existence or the middle-box count. -/
theorem original_finite_topology_canonical_appendices (bbc : PublishedFiniteOneEndDifferentialGeometry)
    (rr : GenusOneCanonicalDivisorFormula.{0}) :
    (∀ s : OriginalPositionallyAsymptoticHelicoid, ∃ W∈positiveUnitPitchFamily, 1/8<W.t ∧
      (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite ∧
    (∀ s : OriginalSmoothHelicoid, ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ (∀ d∈atlas ℂ s.carrier, InducedIsothermalChart s.position d) ∧
      HasInfiniteCompactSurfaceMorseIndex s.position) := by
  have present (s : OriginalPositionallyAsymptoticHelicoid) :
      ∃ W∈positiveUnitPitchFamily, (spatialSimilaritySetoid _).r s.image W.image := by
    obtain ⟨A⟩ := classical_finite_topology_gives_published_one_handle_model bbc s.toOriginalSmoothHelicoid
      s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
    exact positional_poles_give_positive_pitch_representative s A
      (genus_one_period_uniformization_from_canonical_divisor rr _) marked_rhombic_helicoid_intersection
  refine ⟨?_,?_,original_one_handle_index_from_general_end_theorem bbc⟩
  · intro s
    obtain ⟨W,hW,rel⟩ := present s
    exact ⟨W,hW,analytic_pitch_height_gap W,rel⟩
  · apply analytic_pitch_class_finiteness.subset
    rintro _ ⟨s,rfl⟩
    obtain ⟨W,_,rel⟩ := present s
    exact ⟨W,(Quotient.sound rel).symm⟩

/-- A single classical set of published inputs yields the calibrated
unique class on the original smooth surface and global embeddedness of
the explicit root immersion. The input about differential forms gives
only dimension and degree on a genus-one surface. -/
theorem original_unique_certified_class_from_finite_end_rr_existence (bbc : PublishedFiniteOneEndDifferentialGeometry)
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
      p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) :=
  original_manuscript_from_genus_one_riemann_roch (published_finite_one_end_implies_original_exterior bbc) rr whw

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_finite_topology_canonical_appendices
#print axioms TwoAxisHelicoid.original_unique_certified_class_from_finite_end_rr_existence
