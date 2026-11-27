import TwoAxisHelicoid.ImmersedTangentProjection
import TwoAxisHelicoid.EmbeddedSurfaceFieldExtension

namespace TwoAxisHelicoid
open Complex Set Filter Topology Metric
open scoped Topology ContDiff RealInnerProductSpace

/-- A constant ambient unit vector has a globally bounded smooth ambient
extension of its projections on the tangent planes of the original surface. -/
theorem bounded_projected_surface_field {M : Type*} [TopologicalSpace M] (F : M → Fin 3 → ℝ)
    (hF : IsClosedEmbedding F) (e : M → OpenPartialHomeomorph M ℂ) (he : ∀ q, q ∈ (e q).source)
    (hr : ∀ q, RegularImmersionChart F (e q)) {K : Set M} {B : ℝ} (hII : HasBoundedSurfaceWeingarten F e K B)
    {u : SurfaceEuclideanSpace} (hu : ‖u‖ = 1) :
    ∃ V : (Fin 3 → ℝ) → Fin 3 → ℝ, ContDiff ℝ 1 V ∧
      (∀ y, ‖V y‖ ≤ ‖surfaceCartesianEquiv.toContinuousLinearMap‖) ∧
      ∀ q, coordinateToEuclidean (V (F q)) = (chartEuclideanTangent F (e q) (e q q)).starProjection u := by
  classical
  let P := fun q => (chartEuclideanTangent F (e q) (e q q)).starProjection u
  let v := Function.extend F (fun q => surfaceCartesianEquiv (P q)) (fun _ => 0)
  have hv (q : M) : v (F q) = surfaceCartesianEquiv (P q) := hF.injective.extend_apply _ _ q
  let b := ‖surfaceCartesianEquiv.toContinuousLinearMap‖
  have hb (q : M) : v (F q) ∈ closedBall 0 b := by
    rw [mem_closedBall,dist_zero_right,hv]
    have hn : ‖P q‖ ≤ 1 := hu ▸ Submodule.norm_starProjection_apply_le (K := chartEuclideanTangent F (e q) (e q q)) u
    exact (surfaceCartesianEquiv.toContinuousLinearMap.le_opNorm (P q)).trans
      ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _))
  obtain ⟨V,hV,hb',hv'⟩ := embedded_surface_field_extension F hF (convex_closedBall _ _) (mem_closedBall_self (norm_nonneg _)) v hb (by
    intro q
    obtain ⟨n,hn,hcoord,_⟩ := hII q
    have hs : ContDiffAt ℝ 1 (fun w => projectedTangentVelocity u (n w)) (e q q) :=
      contDiffAt_const.sub ((contDiffAt_const.inner ℝ hn).smul hn)
    have hg := surface_projection_chart_germ he hr q u hcoord
    have hsame : v ∘ F ∘ (e q).symm =ᶠ[𝓝 (e q q)] fun w => surfaceCartesianEquiv (projectedTangentVelocity u (n w)) := by
      filter_upwards [hg] with w hw
      exact (hv ((e q).symm w)).trans (congrArg surfaceCartesianEquiv hw)
    have hrc := hr q _ ((e q).map_source (he q))
    exact ⟨e q,he q,hrc.1.of_le (by norm_num),hrc.2,
      (surfaceCartesianEquiv.contDiff.contDiffAt.comp _ hs).congr_of_eventuallyEq hsame⟩)
  exact ⟨V,hV,fun y => by simpa only [mem_closedBall,dist_zero_right] using hb' y,
    fun q => by rw [hv',hv,surfaceEuclidean_toCartesian]⟩

/-- The ambient extension is tangent in each actual coordinate chart,
including on overlaps of two different preferred charts. -/
theorem projected_field_tangent_chart {M : Type*} [TopologicalSpace M] {F : M → Fin 3 → ℝ}
    {e : M → OpenPartialHomeomorph M ℂ} (he : ∀ q, q ∈ (e q).source)
    (hr : ∀ q, RegularImmersionChart F (e q)) {u : SurfaceEuclideanSpace} {V : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hV : ∀ q, coordinateToEuclidean (V (F q)) = (chartEuclideanTangent F (e q) (e q q)).starProjection u)
    {d : OpenPartialHomeomorph M ℂ} (hd : RegularImmersionChart F d) (q : M) (hq : q ∈ d.source) :
    ∃ v : ℂ, fderiv ℝ (F ∘ d.symm) (d q) v = V (F q) := by
  have hm := (chartEuclideanTangent F (e q) (e q q)).starProjection_apply_mem u
  rw [← hV q,chartEuclideanTangent_eq (hr q) hd (he q) hq] at hm
  obtain ⟨v,hv⟩ := hm
  exact ⟨v,surfaceCartesianEquiv.symm.injective hv⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_projected_surface_field
#print axioms TwoAxisHelicoid.projected_field_tangent_chart
