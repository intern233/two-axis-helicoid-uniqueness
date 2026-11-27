import TwoAxisHelicoid.PositionalManuscriptConclusion
import TwoAxisHelicoid.PublishedFiniteTopologyCurvature
import TwoAxisHelicoid.PublishedMarkedEmbeddedExample

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- TwoAxisHelicoid Theorem 1.1 for the original one-sided positional asymptotic
condition, with precisely the general curvature estimate, uniformization
and the independently published marked existence result as inputs. -/
theorem original_manuscript_main_of_published_inputs
    (mp : PublishedFiniteTopologyGaussianCurvature) (poi : SimplyConnectedNoncompactUniformization.{0})
    (whw : PublishedMarkedEmbeddedHelicoidExample) :
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
  theorem_1_1_for_original_positional_ends (original_gaussian_bound_of_finite_topology_publication mp) poi
    ((original_c1_representative_of_published_marked_example whw).map fun s => s.toPositional)

/-- Appendices B and D for each original surface using the same general
curvature theorem and uniformization, independent of embedded existence. -/
theorem positional_appendices_of_published_inputs
    (mp : PublishedFiniteTopologyGaussianCurvature) (poi : SimplyConnectedNoncompactUniformization.{0}) :
    (∀ s : OriginalPositionallyAsymptoticHelicoid, ∃ W∈positiveUnitPitchFamily, 1/8<W.t ∧
      (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite ∧
    (∀ s : OriginalPositionallyAsymptoticHelicoid, ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ (∀ d∈atlas ℂ s.carrier, InducedIsothermalChart s.position d) ∧
      HasInfiniteCompactSurfaceMorseIndex s.position) :=
  positional_geometric_appendices_of_gaussian_bound (original_gaussian_bound_of_finite_topology_publication mp) poi

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_manuscript_main_of_published_inputs
#print axioms TwoAxisHelicoid.positional_appendices_of_published_inputs
