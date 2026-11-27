import TwoAxisHelicoid.FixedCutoffFellCompactness
import TwoAxisHelicoid.FilledTorusDiskComplement

namespace TwoAxisHelicoid
open Set Topology

/-- The original single-cutoff proof of B.1 and B.2 from compactness
and smooth convergence of the Hoffman–White class with its actual
periodic slab. Minimum periods, exclusion of the standard helicoid,
and the topology outside the slab disk are all derived. -/
theorem original_appendix_B_from_single_measured_compact_class {I : Type*} [TopologicalSpace I]
    (η : ℝ) (eta : Real.pi/2<η) (family : FixedAxisHelicoidNormalClass I)
    (compact : IsCompact {m : I | (η : WithTop ℝ)≤physicalScrewHalfPeriod (physicalNormalPositions (family.normal m))})
    (smooth : ContinuousFellOn family.normal {m : I | (η : WithTop ℝ)≤physicalScrewHalfPeriod (physicalNormalPositions (family.normal m))})
    (slab : ∀ m (k : ℝ), η≤k → physicalScrewHalfPeriod (physicalNormalPositions (family.normal m))=(k : WithTop ℝ) →
      (∀ b : ℝ, physicalNormalPositions (family.normal m)≠range (axisRuledHelicoid Complex.I 1 b)) →
      ∃ P : PeriodicSlabNormalMember (family.normal m), P.halfPeriod=k) :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily ∧
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧
      ∀ s : OriginalHelicoidRepresentative, ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite :=
  original_appendix_B_from_physical_period_cutoff embedded_torus_disk_complement_has_open_handle
    η eta family compact smooth slab

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_appendix_B_from_single_measured_compact_class
