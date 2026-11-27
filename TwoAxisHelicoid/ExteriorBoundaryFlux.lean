import TwoAxisHelicoid.ExteriorConormalPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral

namespace TwoAxisHelicoid
open Complex Set Metric MeasureTheory

/-- An ordinary radius-r curve also lives on the closed exterior, so its
flux uses the physical conormal at points of the actual boundary. -/
noncomputable def closedExteriorFluxBoundary (r : ℝ) (hr : 0 < r) :
    ComplexPeriodArc {z : ℂ | r ≤ ‖z‖} where
  left := 0
  right := 2*Real.pi
  ordered := Real.two_pi_pos.le
  curve := circleMap 0 r
  velocity θ := circleMap 0 r θ*I
  stays θ _ := by change r ≤ ‖circleMap 0 r θ‖; rw [norm_circleMap_zero,abs_of_pos hr]
  continuous_curve := (continuous_circleMap _ _).continuousOn
  continuous_velocity := ((continuous_circleMap _ _).mul continuous_const).continuousOn
  derivative θ _ := hasDerivAt_circleMap 0 r θ

private theorem closed_boundary_complex_integral (r : ℝ) (hr : 0 < r) (f : ℂ → ℂ) :
    (closedExteriorFluxBoundary r hr).integral f = circleIntegral f 0 r := by
  simp only [closedExteriorFluxBoundary,ComplexPeriodArc.integral,circleIntegral,deriv_circleMap,smul_eq_mul]

private theorem interior_boundary_complex_integral {r s : ℝ} (hr : 0 < r) (hs : r < s) (f : ℂ → ℂ) :
    (exteriorFluxCircle hr hs).integral f = circleIntegral f 0 s := by
  simp only [exteriorFluxCircle,ComplexPeriodArc.integral,circleIntegral,deriv_circleMap,smul_eq_mul]

/-- On a closed annulus Cauchy's theorem transports the three physical
boundary-flux components to every larger circle. The boundary coefficient
needs continuity there, and holomorphy is used only in the interior. -/
theorem spatial_flux_on_radius_eq_boundary {r s : ℝ} (hr : 0 < r) (hs : r < s)
    (X : ℂ → Fin 3 → ℝ) (p : ℂ → Fin 3 → ℂ)
    (hd : ∀ z : ℂ, r ≤ ‖z‖ → HasFDerivAt X (nullRealDerivative (p z)) z)
    (hn : ∀ z : ℂ, r ≤ ‖z‖ → ComplexNull (p z))
    (hc : ∀ j, ContinuousOn (fun w => p w j) {z : ℂ | r ≤ ‖z‖})
    (hh : ∀ z : ℂ, r < ‖z‖ → ∀ j, DifferentiableAt ℂ (fun w => p w j) z)
    (j : Fin 3) :
    (exteriorFluxCircle hr hs).spatialConormalFlux X j = (closedExteriorFluxBoundary r hr).spatialConormalFlux X j := by
  rw [(exteriorFluxCircle hr hs).spatialConormalFlux_eq_im X p
      (fun z hz => hd z hz.le) (fun z hz => hn z hz.le) j ((hc j).mono fun z (hz : r < ‖z‖) => show r ≤ ‖z‖ from hz.le),
    (closedExteriorFluxBoundary r hr).spatialConormalFlux_eq_im X p hd hn j (hc j),
    interior_boundary_complex_integral,closed_boundary_complex_integral]
  apply congrArg Complex.im
  refine circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hs.le (s := ∅) countable_empty
    ((hc j).mono fun z hz => ?_) (fun z hz => ?_)
  · exact le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hz.2)
  · apply hh z _ j
    exact lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hz.1.2)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatial_flux_on_radius_eq_boundary
