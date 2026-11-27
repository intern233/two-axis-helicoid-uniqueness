import TwoAxisHelicoid.PlacedManuscriptConclusion

namespace TwoAxisHelicoid
open Complex Set Topology

/-- In arbitrary physical positions even the example used for existence
can be unmarked. No Weierstrass coefficients, pole orders, fundamental
curves, or designated position of that example occur as hypotheses. -/
theorem placed_main_of_unmarked_geometric_existence (mp : PublishedFiniteTopologyGaussianCurvature)
    (poi : SimplyConnectedNoncompactUniformization.{0}) (exampleExists : Nonempty PlacedPositionalHelicoid) :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : PlacedPositionalHelicoid, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : PlacedPositionalHelicoid, HasCertifiedPointedNormalization s.normalized.toOriginalSmoothHelicoid ∧
        HasOriginalPointedGaussDivisor s.normalized.toOriginalSmoothHelicoid) ∧
      certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+I*p.t ∧
      p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) := by
  obtain ⟨⟨c,hc,unique⟩,model,embed,normal,calibrated⟩ := theorem_1_1_for_original_positional_ends
    (original_gaussian_bound_of_finite_topology_publication mp) poi (exampleExists.map PlacedPositionalHelicoid.normalized)
  exact ⟨⟨c,(placed_class_iff_original c).mpr hc,fun y h => unique y ((placed_class_iff_original y).mp h)⟩,
    (placed_class_iff_original _).mpr model,embed,fun s => normal s.normalized,calibrated⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.placed_main_of_unmarked_geometric_existence
