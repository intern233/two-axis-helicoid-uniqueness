import TwoAxisHelicoid.TorusMarkingChartGerm
import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange

namespace TwoAxisHelicoid
open Complex Filter Set Topology
open scoped Topology ContDiff Manifold

/-- A pointed biholomorphic torus marking identifies the actual coordinate
at the geometric end with a regular holomorphic germ in the covering
plane. Neither the derivative nor its nonvanishing is an assumption. -/
theorem marked_torus_end_chart_germ {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N]
    {L : PeriodPair} (H : N ≃ₜ PeriodTorus L) (p : N) (h0 : H p = 0)
    (hH : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H) (hi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm)
    (χ : OpenPartialHomeomorph N ℂ) (hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N)
    (hp : p ∈ χ.source) (hz : χ p = 0) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = 0 ∧ deriv u 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (0:ℂ), χ.symm (u z) = H.symm (periodTorusProjection L z) := by
  have hπ0 : periodTorusProjection L 0 = 0 := (periodTorusProjection_eq_zero L 0).mpr L.lattice.zero_mem
  have hf0 : H.symm (periodTorusProjection L 0) = p := H.symm_apply_eq.mpr (hπ0.trans h0.symm)
  obtain ⟨u,hu,hu0,hd,he⟩ := torus_marking_local_coordinate H hH hi χ hχ 0 (hf0.symm ▸ hp)
  exact ⟨u,hu,hu0.trans ((congrArg χ hf0).trans hz),hd,he⟩

/-- Height and Gauss-log end orders computed in the actual surface's local
chart are also their orders in the centered parameter of its marked torus. -/
theorem uniformized_torus_actual_end_orders {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N]
    {L : PeriodPair} (H : N ≃ₜ PeriodTorus L) (p : N) (h0 : H p = 0)
    (hH : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H) (hi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω H.symm)
    (χ : OpenPartialHomeomorph N ℂ) (hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N)
    (hp : p ∈ χ.source) (hz : χ p = 0) (X : N → Fin 3 → ℝ)
    (hreg : ∀ᶠ w in 𝓝[≠] (0:ℂ), DifferentiableAt ℝ (X ∘ χ.symm) w ∧
      DifferentiableAt ℂ (immersionGaussMap (X ∘ χ.symm)) w)
    (hh : MeromorphicAt (fun w => immersionComplexCoefficient (X ∘ χ.symm) w 2) 0)
    (hg : MeromorphicAt (immersionGaussLogDerivative (X ∘ χ.symm)) 0) :
    let Y := X ∘ H.symm ∘ periodTorusProjection L
    MeromorphicAt (fun z => immersionComplexCoefficient Y z 2) 0 ∧
      meromorphicOrderAt (fun z => immersionComplexCoefficient Y z 2) 0 =
        meromorphicOrderAt (fun w => immersionComplexCoefficient (X ∘ χ.symm) w 2) 0 ∧
      MeromorphicAt (immersionGaussLogDerivative Y) 0 ∧ meromorphicOrderAt (immersionGaussLogDerivative Y) 0 =
        meromorphicOrderAt (immersionGaussLogDerivative (X ∘ χ.symm)) 0 := by
  obtain ⟨u,hu,hu0,hn,he⟩ := marked_torus_end_chart_germ H p h0 hH hi χ hχ hp hz
  let Y := X ∘ H.symm ∘ periodTorusProjection L
  have hy : Y =ᶠ[𝓝[≠] (0:ℂ)] (X ∘ χ.symm) ∘ u := by
    filter_upwards [nhdsWithin_le_nhds he] with w hw
    exact congrArg X hw.symm
  have h := actual_end_double_poles_change_coordinate hu hn hy
    (hu0.symm ▸ hreg) (hu0.symm ▸ hh) (hu0.symm ▸ hg)
  simpa only [hu0] using h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.uniformized_torus_actual_end_orders
