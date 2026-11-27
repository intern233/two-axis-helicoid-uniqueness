import TwoAxisHelicoid.CertifiedSlopingCycleCore
import TwoAxisHelicoid.SlopingTriangleEmbeddingTest
import TwoAxisHelicoid.OriginalExistenceCompactCriterion

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Without assuming an embedded example, the original graph-ended
existence problem is equivalent to a spatial collision test with one
parameter in the fixed open triangle and the other in the fundamental
square. All four boundary curves and all their mutual intersections
are already accounted for. -/
theorem certified_triangle_existence_criterion :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let Z := rhombicSlopingPoint p.t
    Nonempty OriginalHelicoidRepresentative ↔
      ∀ x y : ℝ, 0<y → y<x → x+y<1 → ∀ u∈Ico (0:ℝ) 1, ∀ v∈Ico (0:ℝ) 1,
        Z u v∉certifiedPeriodPair.lattice → X (Z x y)=X (Z u v) → u=x ∧ v=y := by
  intro p X Z
  let L := rhombicPeriodPair p.t p.height_pos
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have per := actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X per q.1
  have coord {u v : PuncturedPeriodTorus L} : certifiedTorusImmersion u=certifiedTorusImmersion v ↔ Y u=Y v :=
    ⟨fun e => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective e,fun e => congrArg coordinateToEuclidean e⟩
  have existence : Nonempty OriginalHelicoidRepresentative ↔ Function.Injective Y := by
    constructor
    · rintro ⟨s⟩ u v eq
      exact (pointed_original_embedding_and_similarity s.toOriginalSmoothHelicoid
        (original_graph_poles_cap_and_index s).2.2.1).1.injective (coord.mpr eq)
    · intro hi
      obtain ⟨s,_⟩ := certified_original_representative_of_injective (fun _ _ e => hi (coord.mp e))
      exact ⟨s⟩
  exact existence.trans (sloping_triangle_embedding_test p.height_pos d per
    (fun _ hu _ hv e => certified_axis_and_cycle_injective_core.1 hu hv (coord.mpr e)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_triangle_existence_criterion
