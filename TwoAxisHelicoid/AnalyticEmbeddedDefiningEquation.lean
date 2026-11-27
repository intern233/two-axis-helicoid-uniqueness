import TwoAxisHelicoid.RegularGraphCoordinates
import TwoAxisHelicoid.AnalyticSurfaceContinuation

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff

/-- A spatial analytic left inverse for a regular surface chart, on the
nearby image. It applies in particular to straight lines inside that image. -/
theorem embedded_surface_local_analytic_inverse {M : Type*} [TopologicalSpace M]
    {X : M → Fin 3 → ℝ} (hX : IsEmbedding X)
    (e : OpenPartialHomeomorph M ℂ) {p : M} (hp : p ∈ e.source)
    (hY : AnalyticAt ℝ (X ∘ e.symm) (e p))
    (hi : Function.Injective (fderiv ℝ (X ∘ e.symm) (e p))) :
    ∃ τ : (Fin 3 → ℝ) → ℂ, AnalyticAt ℝ τ (X p) ∧ τ (X p) = e p ∧
      ∀ᶠ v in 𝓝[range X] (X p), X (e.symm (τ v)) = v := by
  let Y := X ∘ e.symm
  let z := e p
  obtain ⟨i,j,_,hm⟩ := regular_immersion_coordinate_minor _ hi
  let P := spatialGraphProjection i j
  let f := P ∘ Y
  let D := P.comp (fderiv ℝ Y z)
  have hf : ContDiffAt ℝ ω f z := P.contDiff.contDiffAt.comp z hY.contDiffAt
  have hD : HasFDerivAt f D z := P.hasFDerivAt.comp z hY.differentiableAt.hasFDerivAt
  have hinj : Function.Injective D := spatialGraphProjection_injective _ _ _ hm
  let D' := (LinearEquiv.ofBijective D.toLinearMap ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hD' : HasFDerivAt f (D' : ℂ →L[ℝ] ℂ) z := hD
  let c := hf.toOpenPartialHomeomorph f hD' (by simp)
  have hc : z ∈ c.source := hf.mem_toOpenPartialHomeomorph_source hD' (by simp)
  have hInv : AnalyticAt ℝ c.symm (f z) := (hf.to_localInverse hD' (by simp)).analyticAt
  have hYz : Y z = X p := congrArg X (e.left_inv hp)
  have hh : c.symm (P (X p)) = z := by rw [← hYz]; exact c.left_inv hc
  have hInv' : AnalyticAt ℝ c.symm (P (X p)) := by rw [← hYz]; exact hInv
  refine ⟨c.symm ∘ P,hInv'.comp (P.analyticAt _),hh,?_⟩
  rw [← hX.map_nhds_eq p]
  change ∀ᶠ u in 𝓝 p, Y (c.symm (P (X u))) = X u
  filter_upwards [e.open_source.mem_nhds hp,(e.continuousAt hp).eventually (c.open_source.mem_nhds hc)]
    with u hu hcu
  have hYu : Y (e u) = X u := congrArg X (e.left_inv hu)
  have hce : c (e u) = P (X u) := by change P (Y (e u)) = _; rw [hYu]
  rw [← hce,c.left_inv hcu,hYu]

/-- A regular real-analytic surface chart of an embedded surface yields
an analytic defining equation for the full nearby image. -/
theorem embedded_analytic_surface_local_equation {M : Type*} [TopologicalSpace M]
    {X : M → Fin 3 → ℝ} (hX : IsEmbedding X)
    (e : OpenPartialHomeomorph M ℂ) {p : M} (hp : p ∈ e.source)
    (hY : AnalyticAt ℝ (X ∘ e.symm) (e p))
    (hi : Function.Injective (fderiv ℝ (X ∘ e.symm) (e p))) :
    ∃ G : (Fin 3 → ℝ) → (Fin 3 → ℝ), AnalyticAt ℝ G (X p) ∧
      ∀ᶠ v in 𝓝 (X p), v ∈ range X ↔ G v = 0 := by
  obtain ⟨τ,hτ,hτp,hnear⟩ := embedded_surface_local_analytic_inverse hX e hp hY hi
  let G := fun v => v-(X ∘ e.symm) (τ v)
  have hYa : AnalyticAt ℝ (X ∘ e.symm) (τ (X p)) := hτp.symm ▸ hY
  refine ⟨G,analyticAt_id.sub (hYa.comp hτ),?_⟩
  rw [eventually_nhdsWithin_iff] at hnear
  filter_upwards [hnear] with v hv
  refine ⟨fun hm => sub_eq_zero.mpr (hv hm).symm,fun he => ?_⟩
  have he' : v = X (e.symm (τ v)) := sub_eq_zero.mp he
  exact ⟨e.symm (τ v),he'.symm⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_analytic_surface_local_equation
