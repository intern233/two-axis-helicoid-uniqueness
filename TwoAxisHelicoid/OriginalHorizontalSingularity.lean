import TwoAxisHelicoid.HorizontalKernelSingularity
import TwoAxisHelicoid.PeriodicCoefficientComplexPrimitive
import TwoAxisHelicoid.TorusHeightFluxMonodromy

namespace TwoAxisHelicoid
open Complex Filter Set Metric
open scoped Topology

/-- The period coefficient of §6.1 has zero *complex* integral around
each lattice puncture, also when its isolated singularity is essential.
The argument works off the vertical solution branch. -/
theorem original_horizontal_puncture_integral {t : ℝ} (ht : 0<t) (a : ℝ) (w : ℂ) :
    ∃ ε>0, ∀ r∈Ioo (0:ℝ) ε, circleIntegral (thetaA t a) w r=0 := by
  let L := rhombicPeriodPair t ht
  obtain ⟨ε,he,sub⟩ := Metric.mem_nhds_iff.mp (L.compl_lattice_sdiff_singleton_mem_nhds w)
  refine ⟨ε,he,fun r hr => periodic_coefficient_circle_integral_zero ht
    (fun _ hz => thetaA_analyticAt_off_lattice ht a hz)
    (fun z ω h => thetaA_add_lattice ht a z ⟨ω,h⟩) w hr.1 ?_⟩
  apply Set.disjoint_left.mpr
  intro z hz h
  exact sub (sphere_subset_ball hr.2 hz) ⟨h,ne_of_mem_sphere hz hr.1.ne'⟩

/-- Path independence on the punctured covering plane, including
closed paths enclosing any finite number of lattice punctures. -/
theorem original_horizontal_arc_primitive {t : ℝ} (ht : 0<t) (a : ℝ) :
    let Ω := ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ
    ∃ F : ℂ → ℂ, (∀ z∈Ω, HasDerivAt F (thetaA t a z) z) ∧
      ∀ b : ComplexPeriodArc Ω, b.integral (thetaA t a)=F (b.curve b.right)-F (b.curve b.left) := by
  obtain ⟨F,d⟩ := periodic_coefficient_unrestricted_complex_primitive ht
    (fun _ hz => thetaA_analyticAt_off_lattice ht a hz)
    (fun z ω h => thetaA_add_lattice ht a z ⟨ω,h⟩)
  exact ⟨F,d,fun b => b.integral_eq_primitive_sub
    (fun _ hz => (thetaA_analyticAt_off_lattice ht a hz).continuousAt.continuousWithinAt) d⟩

/-- Exactly the lattice points are nonmeromorphic for 0<a<1. At
a=1 the coefficient is meromorphic everywhere, by the sigma addition
formula identifying it with the shifted Weierstrass function. -/
theorem original_horizontal_meromorphic_locus {t : ℝ} (ht : 0<t) :
    (∀ a∈Ioo (0:ℝ) 1, ∀ w : ℂ, MeromorphicAt (thetaA t a) w ↔ w∉(rhombicPeriodPair t ht).lattice) ∧
    ∀ w : ℂ, MeromorphicAt (thetaA t 1) w := by
  let L := rhombicPeriodPair t ht
  constructor
  · intro a ha w
    refine ⟨fun h hw => ?_,fun hw => (thetaA_analyticAt_off_lattice ht a hw).meromorphicAt⟩
    have translate : MeromorphicAt (thetaA t a) ((0:ℂ)+w) := by simpa using h
    have translated := translate.comp_analyticAt (f := thetaA t a) (g := fun z : ℂ => z+w)
      (analyticAt_id.add analyticAt_const)
    apply thetaA_not_meromorphic_at_origin ht ha
    exact translated.congr (.of_forall (fun z => thetaA_add_lattice ht a z ⟨w,hw⟩))
  · intro w
    have h : MeromorphicAt (fun z => L.weierstrassP z-L.weierstrassP 1) w :=
      (L.meromorphic_weierstrassP w).sub analyticAt_const.meromorphicAt
    apply h.congr
    filter_upwards [latticePoleSet_punctured_avoids L (finite_singleton (0:ℂ)) w] with z hz
    exact (thetaA_one_eq_weierstrassP ht (fun e => hz ⟨0,rfl,by simpa using e⟩)).symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_horizontal_puncture_integral
#print axioms TwoAxisHelicoid.original_horizontal_arc_primitive
#print axioms TwoAxisHelicoid.original_horizontal_meromorphic_locus
