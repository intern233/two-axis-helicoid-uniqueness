import TwoAxisHelicoid.OriginalPitchNormalization
import TwoAxisHelicoid.CompactnessNormalCoreGraphs

namespace TwoAxisHelicoid
open Set

/-- The compactness-and-flux proof of the parameter gap and of
finiteness in the actual original similarity quotient. The normal graph
input permits a periodic limit and finite multiplicity on a core. -/
theorem original_appendix_B_compactness (bbc : OriginalHelicoidExteriorPrinciple)
    (uniform : ∀ L, CompactGenusOneUniformization.{0} L) (hw : RhombicHelicoidIntersectionPrinciple)
    (compactness : HasLocalNormalGraphLimits embeddedPitchFamily) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ surface : OriginalHelicoidRepresentative, ∃ W ∈ embeddedPitchFamily,
      ε ≤ W.t ∧ (spatialSimilaritySetoid _).r surface.image W.image) ∧
    (range (fun surface : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) surface.image)).Finite := by
  obtain ⟨⟨ε,hε,hgap⟩,hfin⟩ := local_C1_core_compactness_gives_gap_and_finite_images
    (local_normal_graph_limits_supply_core_compactness compactness)
  constructor
  · refine ⟨ε,hε,fun surface => ?_⟩
    obtain ⟨W,hW,hS⟩ := original_representative_in_pitch_family surface bbc (uniform _) hw
    exact ⟨W,hW,hgap W hW,hS⟩
  · apply hfin.subset
    rintro _ ⟨surface,rfl⟩
    obtain ⟨W,hW,hS⟩ := original_representative_in_pitch_family surface bbc (uniform _) hw
    exact ⟨W,hW,(Quotient.sound hS).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_appendix_B_compactness
