import TwoAxisHelicoid.OriginalPitchNormalization
import TwoAxisHelicoid.AnalyticPitchClassFiniteness

namespace TwoAxisHelicoid
open Set

/-- Independently of geometric compactness, the analytic endpoint
estimates give an explicit normalized height gap and finiteness for
the same original geometric classes, without compact-interval boxes. -/
theorem original_appendix_B_by_analytic_endpoints (bbc : OriginalHelicoidExteriorPrinciple)
    (uniform : ∀ L, CompactGenusOneUniformization.{0} L) (hw : RhombicHelicoidIntersectionPrinciple) :
    (∀ surface : OriginalHelicoidRepresentative, ∃ W ∈ embeddedPitchFamily, 1/8 < W.t ∧
      (spatialSimilaritySetoid _).r surface.image W.image) ∧
    (range (fun surface : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) surface.image)).Finite := by
  constructor
  · intro surface
    obtain ⟨W,hW,hS⟩ := original_representative_in_pitch_family surface bbc (uniform _) hw
    exact ⟨W,hW,analytic_pitch_height_gap W,hS⟩
  · apply analytic_pitch_class_finiteness.subset
    rintro _ ⟨surface,rfl⟩
    obtain ⟨W,_,hS⟩ := original_representative_in_pitch_family surface bbc (uniform _) hw
    exact ⟨W,(Quotient.sound hS).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_appendix_B_by_analytic_endpoints
