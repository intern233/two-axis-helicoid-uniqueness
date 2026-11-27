import TwoAxisHelicoid.EuclideanImmersionMetric
import TwoAxisHelicoid.ImmersionLengthDistance
import TwoAxisHelicoid.ProperMetricCompleteness

namespace TwoAxisHelicoid
open Bundle Set Filter Manifold
open scoped Manifold ContDiff Topology Bundle
set_option maxHeartbeats 1000000

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [T3Space M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The length distance of the actual pullback metric, with the original
manifold topology. -/
@[instance_reducible] noncomputable def euclideanImmersionEMetricSpace
    (X : M → E) (hX : ContMDiff I 𝓘(ℝ, E) 1 X)
    (hD : ∀ x, Function.Injective (mvfderiv I X x)) : EMetricSpace M := by
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(euclideanImmersionMetric X hX hD).toRiemannianMetric⟩
  exact EMetricSpace.ofRiemannianMetric I M

/-- Properness of an actual C¹ immersion implies completeness for its
induced Riemannian length distance. No completeness or distance comparison
is assumed as an input. -/
theorem proper_euclideanImmersion_complete
    (X : M → E) (hX : ContMDiff I 𝓘(ℝ, E) 1 X)
    (hD : ∀ x, Function.Injective (mvfderiv I X x)) (hproper : IsProperMap X) :
    let : EMetricSpace M := euclideanImmersionEMetricSpace X hX hD
    CompleteSpace M := by
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(euclideanImmersionMetric X hX hD).toRiemannianMetric⟩
  let : EMetricSpace M := euclideanImmersionEMetricSpace X hX hD
  apply completeSpace_of_proper_distance_decreasing hproper
  intro x y
  change edist (X x) (X y) ≤ riemannianEDist I x y
  exact edist_le_riemannianEDist_of_differential_bound hX
    (fun z v => (euclideanImmersionMetric_norm X hX hD z v).symm.le) x y

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.proper_euclideanImmersion_complete
