import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace TwoAxisHelicoid
open Bundle Bornology Set
open scoped Manifold Topology Bundle
set_option maxHeartbeats 1000000

variable {B : Type*} {V : B → Type*}
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsNormableSpace ℝ (V x)]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The positive definite pullback of the Euclidean scalar product under
actual injective differentials. The left inverse supplies bounded unit
balls in the original tangent-space topology. -/
noncomputable def pullbackRiemannianMetric (D : ∀ x, V x →L[ℝ] E)
    (hD : ∀ x, (D x).HasLeftInverse) : RiemannianMetric V where
  inner x := (innerSL ℝ (E := E)).bilinearComp (D x) (D x)
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.mpr (fun h => hv ((hD x).injective (h.trans (map_zero (D x)).symm)))
  continuousAt x := ((D x).continuous.inner (D x).continuous).continuousAt
  isVonNBounded x := by
    apply ((NormedSpace.isVonNBounded_ball ℝ E 1).image (hD x).leftInverse).subset
    intro v hv
    refine ⟨D x v,?_,(hD x).leftInverse_leftInverse v⟩
    change inner ℝ (D x v) (D x v) < 1 at hv
    rw [real_inner_self_eq_norm_sq] at hv
    simp only [Metric.mem_ball,dist_zero_right]
    nlinarith [norm_nonneg (D x v)]

@[simp] theorem pullbackRiemannianMetric_inner (D : ∀ x, V x →L[ℝ] E)
    (hD : ∀ x, (D x).HasLeftInverse) (x : B) (v w : V x) :
    (pullbackRiemannianMetric D hD).inner x v w = inner ℝ (D x v) (D x w) := rfl

/-- With the constructed metric, the actual differential preserves norms. -/
theorem pullbackRiemannianMetric_norm (D : ∀ x, V x →L[ℝ] E)
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousConstSMul ℝ (V x)]
    (hD : ∀ x, (D x).HasLeftInverse) (x : B) (v : V x) :
    let : RiemannianBundle V := ⟨pullbackRiemannianMetric D hD⟩
    ‖v‖ = ‖D x v‖ := by
  let : RiemannianBundle V := ⟨pullbackRiemannianMetric D hD⟩
  change ‖v‖ = ‖D x v‖
  rw [norm_eq_sqrt_real_inner,norm_eq_sqrt_real_inner]
  rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.pullbackRiemannianMetric_norm
