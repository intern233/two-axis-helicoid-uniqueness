import TwoAxisHelicoid.HolomorphicEndGeodesic
import TwoAxisHelicoid.ExteriorPotentialIndex

namespace TwoAxisHelicoid
open Complex Real Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

theorem analytic_height_end_derivative_control (α : ℝ) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    ∀ᶠ z in cobounded ℂ,
      AnalyticAt ℂ (fun z => I*(α : ℂ)*z+infinityCorrection f z) z ∧
      ‖deriv (fun z => I*(α : ℂ)*z+infinityCorrection f z) z‖ ≤ |α|+1 := by
  have hs : ∀ᶠ z in cobounded ℂ, ‖deriv (infinityCorrection f) z‖ < 1 := by
    simpa only [Metric.mem_ball,dist_zero_right] using
      (infinityCorrection_deriv_tendsto_zero hf).eventually
        (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1))
  filter_upwards [infinityCorrection_eventually_analytic hf,hs] with z hz hn
  refine ⟨(analyticAt_const.mul analyticAt_id).add hz,?_⟩
  have hd := ((hasDerivAt_id z).const_mul (I*(α : ℂ))).add hz.differentiableAt.hasDerivAt
  change HasDerivAt (fun w => I*(α : ℂ)*w+infinityCorrection f w)
    (I*(α : ℂ)*1+deriv (infinityCorrection f) z) z at hd
  rw [hd.deriv]
  simp only [mul_one]
  have hh := norm_add_le (I*(α : ℂ)) (deriv (infinityCorrection f) z)
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hh
  linarith

/-- Actual unit geodesic segments on every sufficiently far analytic
helicoidal end, with no geodesic-existence hypothesis. -/
theorem analytic_helicoidal_end_unit_geodesics (α R₀ : ℝ) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧
      (∀ z : ℂ, R < ‖z‖ →
        AnalyticAt ℂ (fun w => I*(α : ℂ)*w+infinityCorrection f w) z ∧
        ‖deriv (fun w => I*(α : ℂ)*w+infinityCorrection f w) z‖ ≤ |α|+1) ∧
      ∀ z₀ v₀ : ℂ, R+4 < ‖z₀‖ →
        (Real.cosh (I*(α : ℂ)*z₀+infinityCorrection f z₀).re)^2*Complex.normSq v₀ = 1 →
        ∃ z v : ℝ → ℂ, z 0 = z₀ ∧ v 0 = v₀ ∧
          ∀ t ∈ Icc (0 : ℝ) 1,
            R+2 < ‖z t‖ ∧ HasDerivAt z (v t) t ∧
            HasDerivAt v (-(logGaussConnection
              (fun w => I*(α : ℂ)*w+infinityCorrection f w) (z t)*(v t)^2)) t ∧
            (Real.cosh (I*(α : ℂ)*z t+infinityCorrection f (z t)).re)^2*Complex.normSq (v t) = 1 ∧
            ‖v t‖ ≤ 1 := by
  obtain ⟨B,_hB,hB⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
    (analytic_height_end_derivative_control α hf)
  let R := max B (max (R₀+1) 1)
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans (le_max_right _ _))
  have hRbase : R₀ < R := by
    have h := (le_max_left (R₀+1) 1).trans (le_max_right B (max (R₀+1) 1))
    dsimp [R]
    linarith
  have hcontrol z (hz : R < ‖z‖) := hB ((le_max_left _ _).trans hz.le)
  refine ⟨R,hRbase,hR0,hcontrol,?_⟩
  intro z₀ v₀ hz₀ hv₀
  exact holomorphic_height_end_unit_geodesic hR0.le (by positivity)
    (fun z hz => (hcontrol z hz).1) (fun z hz => (hcontrol z hz).2) z₀ v₀ hz₀ hv₀

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_helicoidal_end_unit_geodesics
