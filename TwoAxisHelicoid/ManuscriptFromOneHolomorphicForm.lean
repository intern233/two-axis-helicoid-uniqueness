import TwoAxisHelicoid.GenusOneHolomorphicFormExistence
import TwoAxisHelicoid.CanonicalSpinCapFromFiniteEnd

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- The finite-topology end theorem, existence of a holomorphic form
on each marked compact handle, and a published embedded example give
the original positional classification, the pointed spin cap for each
candidate, and embeddedness at the certified parameters. -/
theorem original_manuscript_from_one_holomorphic_form (bbc : PublishedFiniteOneEndDifferentialGeometry)
    (form : GenusOneHasHolomorphicDifferential.{0}) (whw : PublishedMarkedEmbeddedHelicoidExample) :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : OriginalPositionallyAsymptoticHelicoid, HasPointedOriginalSpinBranchCap s ∧
        HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧ HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid) ∧
      certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+I*p.t ∧
      p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) := by
  have rr := genus_one_canonical_divisor_of_one_section form
  obtain ⟨unique,model,closed,_,periods⟩ := original_unique_certified_class_from_finite_end_rr_existence bbc rr whw
  exact ⟨unique,model,closed,original_canonical_cap_from_finite_end bbc rr,periods⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_manuscript_from_one_holomorphic_form
