import TwoAxisHelicoid.FiniteTopologyCurvatureClassification

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

private theorem finite_topology_shape_bound (mp : FiniteTopologyGaussianCurvatureBound)
    (s : OriginalPositionallyAsymptoticHelicoid) : HasBoundedPhysicalEndCurvature s.toOriginalSmoothHelicoid := by
  obtain ⟨C,hC,bound⟩ := mp s.toOriginalSmoothHelicoid
  exact original_physical_shape_bound_of_gaussian s.toOriginalSmoothHelicoid hC bound

/-- The spatial class, embedded model, pointed marking, Gauss divisor,
and both rational parameter intervals in Theorem 1.1, starting with
one-sided positional asymptotics on each original surface. -/
theorem theorem_1_1_for_original_positional_ends
    (mp : FiniteTopologyGaussianCurvatureBound) (uni : SimplyConnectedNoncompactUniformization.{0})
    (whw : Nonempty OriginalPositionallyAsymptoticHelicoid) :
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
  obtain ⟨unique,embedded⟩ := positional_unique_class_of_published_gaussian_bound mp uni whw
  have actual := theorem_1_1_for_original_c1_graphs uni (whw.map fun s => s.graphRepresentative (finite_topology_shape_bound mp s))
  obtain ⟨t,ht⟩ := actual.2.1
  exact ⟨unique,⟨t.toPositional,ht⟩,embedded,fun s => (positional_manuscript_calibration s mp uni).2,actual.2.2.2.2⟩

/-- The endpoint gap, finiteness and infinite Morse index also hold for
every original positional representative, without a horizontal box
certificate or any existence hypothesis on the class. -/
theorem positional_geometric_appendices_of_gaussian_bound
    (mp : FiniteTopologyGaussianCurvatureBound) (uni : SimplyConnectedNoncompactUniformization.{0}) :
    (∀ s : OriginalPositionallyAsymptoticHelicoid, ∃ W∈positiveUnitPitchFamily, 1/8<W.t ∧
      (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite ∧
    (∀ s : OriginalPositionallyAsymptoticHelicoid, ∃ S : ChartedSpace ℂ s.carrier, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω s.carrier ∧ (∀ d∈atlas ℂ s.carrier, InducedIsothermalChart s.position d) ∧
      HasInfiniteCompactSurfaceMorseIndex s.position) := by
  let g := fun s : OriginalPositionallyAsymptoticHelicoid => s.graphRepresentative (finite_topology_shape_bound mp s)
  obtain ⟨gap,fin⟩ := original_graph_appendix_B uni
  refine ⟨fun s => gap (g s),fin.subset ?_,fun s => original_graph_infinite_morse_index (g s) uni⟩
  rintro x ⟨s,rfl⟩
  exact ⟨g s,rfl⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.theorem_1_1_for_original_positional_ends
#print axioms TwoAxisHelicoid.positional_geometric_appendices_of_gaussian_bound
