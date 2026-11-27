import TwoAxisHelicoid.SmoothMarkedCircleClass
import TwoAxisHelicoid.HarmonicCircleCotangent
import TwoAxisHelicoid.GenusOneHolomorphicFormExistence

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold
universe u

/-- The flat-circle case of Eells and Sampson, *Harmonic mappings of
Riemannian manifolds*, Amer. J. Math. 86 (1964), §4D, pp. 128–129.
On a Riemann surface harmonicity of a real local angle is expressed in
the given conformal coordinates. No genus or canonical-form datum
occurs in this input. -/
def CompactSurfaceHarmonicCircleRepresentatives : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] (φ : C(M,OrientationCircle)),
    ∃ ψ : C(M,OrientationCircle), ContinuousMap.Homotopic φ ψ ∧ HasLocalHarmonicArguments ψ

theorem circle_real_lift_transport {M : Type*} [TopologicalSpace M] {φ ψ : C(M,OrientationCircle)}
    (hom : ContinuousMap.Homotopic φ ψ) (l : C(M,ℝ)) (lift : ∀ x, (l x : OrientationCircle)=φ x) :
    ∃ g : C(M,ℝ), ∀ x, (g x : OrientationCircle)=ψ x := by
  obtain ⟨H⟩ := hom
  let co := AddCircle.isCoveringMap_coe (1:ℝ)
  have hz (x : M) : H.toContinuousMap (0,x)=(l x:OrientationCircle) := (H.map_zero_left x).trans (lift x).symm
  let G := co.liftHomotopy H.toContinuousMap l hz
  refine ⟨⟨fun x => G (1,x),G.continuous.comp (continuous_const.prodMk continuous_id)⟩,fun x => ?_⟩
  have eq := congrFun (co.liftHomotopy_lifts H.toContinuousMap l hz) (1,x)
  exact eq.trans (H.map_one_left x)

/-- A harmonic representative of the topologically constructed phase
gives a nonzero holomorphic differential on every compact marked
handle. All downstream divisor and uniformization statements then
follow from the plane degree computation. -/
theorem genus_one_one_form_of_harmonic_circle_representatives
    (h : CompactSurfaceHarmonicCircleRepresentatives.{u}) : GenusOneHasHolomorphicDifferential.{u} := by
  intro L M top compact sep atlas manifold marking
  obtain ⟨mark⟩ := marking
  let _ : ConnectedSpace (PeriodTorus L) := (Quotient.mk_surjective :
    Function.Surjective (periodTorusProjection L)).connectedSpace QuotientAddGroup.continuous_mk
  let _ : ConnectedSpace M := mark.symm.surjective.connectedSpace mark.symm.continuous
  obtain ⟨g,_,smooth,non,_,noLift⟩ := smooth_nonliftable_circle_class mark
  let φ : C(M,OrientationCircle) := ⟨planeOrientationDirection ∘ g,continuous_iff_continuousAt.mpr
    fun x => (planeOrientationDirection_continuousAt (non x)).comp smooth.continuous.continuousAt⟩
  obtain ⟨ψ,hom,harmonic⟩ := h M φ
  apply harmonic_nonliftable_phase_gives_holomorphic_section harmonic
  rintro ⟨l,hl⟩
  exact noLift (circle_real_lift_transport hom.symm l hl)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.genus_one_one_form_of_harmonic_circle_representatives
