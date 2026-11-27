import TwoAxisHelicoid.ImmersionPullbackMetric
import Mathlib.Topology.VectorBundle.Hom

namespace TwoAxisHelicoid
open Bundle Bornology Set Filter ContinuousLinearMap
open scoped Topology
set_option maxHeartbeats 1000000

theorem continuousAt_pullback_inner
    {B : Type*} [TopologicalSpace B] {F E : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D : B → F →L[ℝ] E} {x : B} (hD : ContinuousAt D x) :
    ContinuousAt (fun y => (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (D y) (D y)) x := by
  have h₁ : ContinuousAt (fun y => (innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ).comp (D y)) x :=
    continuousAt_const.clm_comp hD
  have h₂ : ContinuousAt (fun y => ((innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ).comp (D y)).flip) x :=
    (ContinuousLinearMap.flipₗᵢ ℝ F E ℝ).continuous.continuousAt.comp h₁
  have h₃ := h₂.clm_comp hD
  exact (ContinuousLinearMap.flipₗᵢ ℝ F F ℝ).continuous.continuousAt.comp h₃

variable {B : Type*} [TopologicalSpace B] {V : B → Type*}
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsNormableSpace ℝ (V x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- Pulling back a fixed inner product is continuous if the actual family
of differentials is continuous in local bundle coordinates. -/
theorem pullback_metric_section_continuous (D : ∀ x, V x →L[ℝ] E)
    (hcoords : ∀ x, ContinuousAt
      (fun y => (D y).comp ((trivializationAt F V x).symmL ℝ y)) x) :
    Continuous (fun x => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
      (E := fun y => V y →L[ℝ] V y →L[ℝ] ℝ) x
      ((innerSL ℝ (E := E) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (D x) (D x))) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [FiberBundle.continuousAt_section]
  have h := continuousAt_pullback_inner (hcoords x)
  apply h.congr_of_eventuallyEq
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy
  rw [hom_trivializationAt_apply]
  ext v w
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  simp [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,
    Trivialization.symmL_apply,hy]

noncomputable def continuousPullbackRiemannianMetric (D : ∀ x, V x →L[ℝ] E)
    (hD : ∀ x, (D x).HasLeftInverse)
    (hcoords : ∀ x, ContinuousAt
      (fun y => (D y).comp ((trivializationAt F V x).symmL ℝ y)) x) :
    ContinuousRiemannianMetric F V where
  inner := (pullbackRiemannianMetric D hD).inner
  symm := (pullbackRiemannianMetric D hD).symm
  pos := (pullbackRiemannianMetric D hD).pos
  isVonNBounded := (pullbackRiemannianMetric D hD).isVonNBounded
  continuous := pullback_metric_section_continuous D hcoords

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.continuousPullbackRiemannianMetric
