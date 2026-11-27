import TwoAxisHelicoid.AbelianOrderWinding
import TwoAxisHelicoid.AbelianIntegralBoundaryDegree
import TwoAxisHelicoid.DegreeOnePlaneFibers

namespace TwoAxisHelicoid.HolomorphicCoefficientDisks
open Complex Set Filter Topology Function
open scoped Topology ContDiff Manifold

/-- On a compact topological torus any holomorphic one-form that is
nonzero somewhere is nowhere zero. Its abelian integral has winding
one at infinity and positive local holomorphic multiplicities. -/
theorem compact_torus_nonzero_form_nowhere_zero {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [CompactSpace M] {L : PeriodPair} (mark : M ≃ₜ PeriodTorus L)
    (A : HolomorphicCoefficientDisks M) (compat : A.compatibleOneForm) {x : M} (nonzero : A.coefficient x (chartAt ℂ x x)≠0) :
    ∀ y, A.coefficient y (chartAt ℂ y y)≠0 := by
  let p := mark.symm ∘ periodTorusProjection L
  have cov : IsCoveringMap p := (periodTorusProjection_isCoveringMap L).homeomorph_comp mark.symm
  have onto : Surjective p := mark.symm.surjective.comp (Quotient.mk_surjective : Surjective (periodTorusProjection L))
  obtain ⟨D,E,B,dev,prop,bound,_,_⟩ := abelian_integral_full_period_lattice mark A compat nonzero
  let P := p ∘ E.symm
  let F := D ∘ E.symm
  have cover : IsCoveringMap P := cov.comp_homeomorph E.symm.toHomeomorph
  have proper : IsProperMap F := prop.comp E.symm.toHomeomorph.isProperMap
  have growth : A.IsAbelianIntegral P F := by
    intro i z h
    exact E.symm.continuous.continuousAt.eventually (dev i (E.symm z) h)
  obtain ⟨op,_,finite⟩ := proper_abelian_integral_open_finite cover growth proper
  obtain ⟨s,k,unit,loc,detect⟩ := abelian_integral_local_multiplicities cover growth op
  have outer (c : ℂ) : ∀ᶠ r : ℝ in atTop,
      HasOrientationCircleDegree (fun a => planeOrientationDirection (F (r • orientationRay a)-c)) 1 := by
    filter_upwards [eventually_gt_atTop (B+‖c‖)] with r large
    exact (bounded_period_displacement_degree_one prop.continuous E bound c large).2
  have noBranch := (degree_one_plane_fibers proper.continuous finite unit k loc outer).2.2
  intro y
  obtain ⟨z,rfl⟩ := (onto.comp E.symm.surjective : Surjective P) y
  exact detect z (noBranch z)

end TwoAxisHelicoid.HolomorphicCoefficientDisks
#print axioms TwoAxisHelicoid.HolomorphicCoefficientDisks.compact_torus_nonzero_form_nowhere_zero
