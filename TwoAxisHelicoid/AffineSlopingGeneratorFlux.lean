import TwoAxisHelicoid.AffineGeneratorFlux
import TwoAxisHelicoid.SlopingGeneratorFluxPlane

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Both actual quotient generators realize the transformed period
vectors, in the original Euclidean axes of any second parametrization
with the stated affine coordinate differential. -/
theorem affine_sloping_generators_actual_fluxes {t a c : ℝ} (ht : 0<t)
    (Z : PuncturedPeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
    (T : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (dz : ∀ z∉(rhombicPeriodPair t ht).lattice, HasFDerivAt (puncturedTorusPullback _ Z)
      (T.comp (nullRealDerivative (coordinateData t a c ht z))) z)
    (null : ∀ z∉(rhombicPeriodPair t ht).lattice, ConformalCoordinateDerivatives (puncturedTorusPullback _ Z) z) :
    let L := rhombicPeriodPair t ht
    let actual := fun w : Fin 3 → ℂ => ∃ (q : PuncturedPeriodTorus L) (γ : Path q q),
      ∀ j, TorusSpatialConormalIntegral L Z j γ (T (fun k => (w k).im) j)
    actual (originalCoordinatePeriod t a c ht) ∧ actual (conjugateCoordinatePeriod t a c ht) := by
  let L := rhombicPeriodPair t ht
  let f := coordinateData t a c ht
  have pc (j : Fin 3) : ContinuousOn (fun z => f z j) (L.lattice : Set ℂ)ᶜ := fun z hz =>
    ((analyticAt_pi_iff.mp (coordinateData_analyticAt (a := a) (c := c) ht hz) j).continuousAt).continuousWithinAt
  have actual (w : Fin 3 → ℂ) (A : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ)
      (cl : periodTorusProjection L (A.curve A.left)=periodTorusProjection L (A.curve A.right))
      (val : ∀ j, A.integral (fun z => f z j)=w j) :
      ∃ (q : PuncturedPeriodTorus L) (γ : Path q q), ∀ j, TorusSpatialConormalIntegral L Z j γ (T (fun k => (w k).im) j) := by
    have eq : A.start=A.finish := Subtype.ext cl
    refine ⟨A.start,A.projected.cast rfl eq,?_⟩
    intro j
    have measure := A.affine_spatial_flux f pc T dz null j
    simp_rw [val] at measure
    rw [← measure]
    exact .arc _ A (fun _ => rfl)
  obtain ⟨⟨A,hA,mA⟩,B,hB,mB⟩ := sloping_generator_parameter_arcs (a := a) (c := c) ht
  exact ⟨actual _ A hA mA,actual _ B hB mB⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.affine_sloping_generators_actual_fluxes
