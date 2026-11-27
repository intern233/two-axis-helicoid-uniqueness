import TwoAxisHelicoid.AnalyticEmbeddedDefiningEquation

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff

/-- A regular parametrized analytic surface has an analytic inverse on its
own local sheet, without global injectivity of the parametrization. -/
theorem regular_analytic_surface_local_inverse {Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hY : AnalyticAt ℝ Y z) (hi : Function.Injective (fderiv ℝ Y z)) :
    ∃ τ : (Fin 3 → ℝ) → ℂ, AnalyticAt ℝ τ (Y z) ∧
      ∀ᶠ w in 𝓝 z, τ (Y w) = w := by
  obtain ⟨i,j,_,hm⟩ := regular_immersion_coordinate_minor _ hi
  let P := spatialGraphProjection i j
  let f := P ∘ Y
  let D := P.comp (fderiv ℝ Y z)
  have hf : ContDiffAt ℝ ω f z := P.contDiff.contDiffAt.comp z hY.contDiffAt
  have hD : HasFDerivAt f D z := P.hasFDerivAt.comp z hY.differentiableAt.hasFDerivAt
  have hinj : Function.Injective D := spatialGraphProjection_injective _ _ _ hm
  let D' := (LinearEquiv.ofBijective D.toLinearMap ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hD' : HasFDerivAt f (D' : ℂ →L[ℝ] ℂ) z := hD
  let e := hf.toOpenPartialHomeomorph f hD' (by simp)
  have he : z ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hD' (by simp)
  have hInv : AnalyticAt ℝ e.symm (f z) := (hf.to_localInverse hD' (by simp)).analyticAt
  have hInv' : AnalyticAt ℝ e.symm (P (Y z)) := hInv
  refine ⟨e.symm ∘ P,hInv'.comp (P.analyticAt _),?_⟩
  filter_upwards [e.open_source.mem_nhds he] with w hw
  exact e.left_inv hw

/-- A continuous lift through any regular real analytic surface is analytic
where its represented spatial map is analytic. -/
theorem continuous_regular_surface_lift_analytic {Y V : ℂ → Fin 3 → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hY : AnalyticAt ℝ Y (F z)) (hi : Function.Injective (fderiv ℝ Y (F z)))
    (hV : AnalyticAt ℝ V z) (hF : ContinuousAt F z)
    (he : ∀ᶠ w in 𝓝 z, Y (F w) = V w) : AnalyticAt ℝ F z := by
  obtain ⟨τ,hτ,hleft⟩ := regular_analytic_surface_local_inverse hY hi
  have hz := he.self_of_nhds
  have ht : AnalyticAt ℝ τ (V z) := hz ▸ hτ
  apply (ht.comp hV).congr
  filter_upwards [he,hF.eventually hleft] with w hw hFw
  change τ (V w) = F w
  rw [← hw,hFw]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.continuous_regular_surface_lift_analytic
