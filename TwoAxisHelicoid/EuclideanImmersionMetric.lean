import TwoAxisHelicoid.ImmersionPullbackMetricContinuity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

namespace TwoAxisHelicoid
open Bundle Set Filter
open scoped Manifold ContDiff Topology Bundle
set_option maxHeartbeats 1000000

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

instance tangentSpaceIsNormable (x : M) : IsNormableSpace ℝ (TangentSpace I x) := by
  change IsNormableSpace ℝ F
  infer_instance

/-- Continuity of the actual differential in fixed tangent coordinates is
derived from the actual map being C¹. -/
theorem immersion_differential_coordinates_continuous {X : M → E}
    (hX : ContMDiff I 𝓘(ℝ, E) 1 X) (x : M) :
    ContinuousAt (fun y => (mvfderiv I X y).comp
      ((trivializationAt F (TangentSpace I) x).symmL ℝ y)) x := by
  have h := ((hX x).mfderiv_const (m := 0) (by norm_num)).continuousAt
  simpa +unfoldPartialApp only [inTangentCoordinates,ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space,ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp,mvfderiv,ContinuousLinearMap.comp_assoc] using! h

/-- The actual induced continuous Riemannian metric of a C¹ immersion in a
finite-dimensional Euclidean space. -/
noncomputable def euclideanImmersionMetric [FiniteDimensional ℝ E]
    (X : M → E) (hX : ContMDiff I 𝓘(ℝ, E) 1 X)
    (hD : ∀ x, Function.Injective (mvfderiv I X x)) :
    ContinuousRiemannianMetric F (TangentSpace I : M → Type _) :=
  continuousPullbackRiemannianMetric (mvfderiv I X)
    (fun x => ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional (hD x))
    (immersion_differential_coordinates_continuous hX)

theorem euclideanImmersionMetric_norm [FiniteDimensional ℝ E]
    (X : M → E) (hX : ContMDiff I 𝓘(ℝ, E) 1 X)
    (hD : ∀ x, Function.Injective (mvfderiv I X x)) (x : M) (v : TangentSpace I x) :
    let : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(euclideanImmersionMetric X hX hD).toRiemannianMetric⟩
    ‖v‖ = ‖mvfderiv I X x v‖ := by
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(euclideanImmersionMetric X hX hD).toRiemannianMetric⟩
  change ‖v‖ = ‖mvfderiv I X x v‖
  rw [norm_eq_sqrt_real_inner,norm_eq_sqrt_real_inner]
  rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.immersion_differential_coordinates_continuous
#print axioms TwoAxisHelicoid.euclideanImmersionMetric_norm
