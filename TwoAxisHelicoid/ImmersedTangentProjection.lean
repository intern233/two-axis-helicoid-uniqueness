import TwoAxisHelicoid.ProjectedTangentVelocity
import TwoAxisHelicoid.ImmersionAtlas
import TwoAxisHelicoid.NullEuclideanMetric
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

abbrev SurfaceEuclideanSpace := EuclideanSpace ℝ (Fin 3)

noncomputable def surfaceCartesianEquiv : SurfaceEuclideanSpace ≃L[ℝ] (Fin 3 → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

theorem surfaceCartesian_toEuclidean (v : Fin 3 → ℝ) : surfaceCartesianEquiv (coordinateToEuclidean v) = v :=
  surfaceCartesianEquiv.apply_symm_apply v

theorem surfaceEuclidean_toCartesian (v : SurfaceEuclideanSpace) : coordinateToEuclidean (surfaceCartesianEquiv v) = v :=
  surfaceCartesianEquiv.symm_apply_apply v

/-- The actual Euclidean tangent plane in an immersion chart. -/
noncomputable def chartEuclideanTangent {M : Type*} [TopologicalSpace M] (F : M → Fin 3 → ℝ)
    (e : OpenPartialHomeomorph M ℂ) (z : ℂ) : Submodule ℝ SurfaceEuclideanSpace :=
  LinearMap.range (coordinateToEuclidean.comp (fderiv ℝ (F ∘ e.symm) z)).toLinearMap

private theorem chartEuclideanTangent_le {M : Type*} [TopologicalSpace M] {F : M → Fin 3 → ℝ}
    {e d : OpenPartialHomeomorph M ℂ} (he : RegularImmersionChart F e) (hd : RegularImmersionChart F d)
    {q : M} (hq : q ∈ e.source) (hq' : q ∈ d.source) :
    chartEuclideanTangent F e (e q) ≤ chartEuclideanTangent F d (d q) := by
  let u := e.symm.trans d
  have hs : e q ∈ u.source := ⟨e.map_source hq,by change e.symm (e q) ∈ d.source; rwa [e.left_inv hq]⟩
  have hu := (regularImmersionChart_transition he hd hs).differentiableAt (by simp)
  have h0 : u (e q) = d q := congrArg d (e.left_inv hq)
  have hY := (hd (d q) (d.map_source hq')).1.differentiableAt (by simp)
  have hY' : DifferentiableAt ℝ (F ∘ d.symm) (u (e q)) := h0.symm ▸ hY
  have hg : F ∘ e.symm =ᶠ[𝓝 (e q)] (F ∘ d.symm) ∘ u := by
    filter_upwards [u.open_source.mem_nhds hs] with w hw
    exact congrArg F (d.left_inv hw.2).symm
  have hD := hg.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp _ hY' hu,h0] at hD
  rintro y ⟨v,rfl⟩
  refine ⟨fderiv ℝ u (e q) v,?_⟩
  change coordinateToEuclidean (fderiv ℝ (F ∘ d.symm) (d q) _) = coordinateToEuclidean (fderiv ℝ (F ∘ e.symm) (e q) v)
  rw [hD]
  rfl

/-- The two tangent planes at a point of overlap agree, for charts of
the actual regular immersion. -/
theorem chartEuclideanTangent_eq {M : Type*} [TopologicalSpace M] {F : M → Fin 3 → ℝ}
    {e d : OpenPartialHomeomorph M ℂ} (he : RegularImmersionChart F e) (hd : RegularImmersionChart F d)
    {q : M} (hq : q ∈ e.source) (hq' : q ∈ d.source) :
    chartEuclideanTangent F e (e q) = chartEuclideanTangent F d (d q) :=
  le_antisymm (chartEuclideanTangent_le he hd hq hq') (chartEuclideanTangent_le hd he hq' hq)

/-- Local unit normal coordinates for the second fundamental form:
the norm of the derivative of the Gauss map on each tangent direction
is bounded by B times that direction's spatial length away from K. -/
def HasBoundedSurfaceWeingarten {M : Type*} [TopologicalSpace M] (F : M → Fin 3 → ℝ)
    (e : M → OpenPartialHomeomorph M ℂ) (K : Set M) (B : ℝ) : Prop :=
  ∀ q, ∃ n : ℂ → SurfaceEuclideanSpace, ContDiffAt ℝ 1 n (e q q) ∧
    (∀ᶠ w in 𝓝 (e q q), ‖n w‖ = 1 ∧ ∀ y : SurfaceEuclideanSpace,
      y ∈ chartEuclideanTangent F (e q) w ↔ ⟪y,n w⟫ = 0) ∧
    (q ∉ K → ∀ v : ℂ, ‖fderiv ℝ n (e q q) v‖ ≤ B*‖coordinateToEuclidean (fderiv ℝ (F ∘ (e q).symm) (e q q) v)‖)

theorem surface_starProjection_from_normal (T : Submodule ℝ SurfaceEuclideanSpace) (u n : SurfaceEuclideanSpace)
    (hn : ‖n‖ = 1) (ht : ∀ y : SurfaceEuclideanSpace, y ∈ T ↔ ⟪y,n⟫ = 0) :
    T.starProjection u = projectedTangentVelocity u n := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (ht _).mpr (projectedTangentVelocity_orthogonal u hn)
  · intro w hw
    rw [projectedTangentVelocity,sub_sub_cancel,real_inner_smul_left,real_inner_comm w n,(ht w).mp hw,mul_zero]

/-- The intrinsic projection field of a constant vector can be computed
in any local chart from either of its two unit normals. -/
theorem surface_projection_chart_germ {M : Type*} [TopologicalSpace M] {F : M → Fin 3 → ℝ}
    {e : M → OpenPartialHomeomorph M ℂ} (he : ∀ q, q ∈ (e q).source)
    (hr : ∀ q, RegularImmersionChart F (e q)) (q : M) (u : SurfaceEuclideanSpace) {n : ℂ → SurfaceEuclideanSpace}
    (hn : ∀ᶠ w in 𝓝 (e q q), ‖n w‖ = 1 ∧ ∀ y, y ∈ chartEuclideanTangent F (e q) w ↔ ⟪y,n w⟫ = 0) :
    (fun w => let p := (e q).symm w; (chartEuclideanTangent F (e p) (e p p)).starProjection u) =ᶠ[𝓝 (e q q)]
      fun w => projectedTangentVelocity u (n w) := by
  filter_upwards [hn,(e q).open_target.mem_nhds ((e q).map_source (he q))] with w hw ht
  let p := (e q).symm w
  have h := chartEuclideanTangent_eq (hr p) (hr q) (he p) ((e q).map_target ht)
  change chartEuclideanTangent F (e p) (e p p) = chartEuclideanTangent F (e q) ((e q) ((e q).symm w)) at h
  rw [(e q).right_inv ht] at h
  change (chartEuclideanTangent F (e p) (e p p)).starProjection u = _
  rw [h]
  exact surface_starProjection_from_normal _ _ _ hw.1 hw.2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.surface_projection_chart_germ
