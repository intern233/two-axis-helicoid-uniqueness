import TwoAxisHelicoid.ConformalExteriorGeodesic
import TwoAxisHelicoid.ExteriorSmoothCutoff
import TwoAxisHelicoid.LogGaussMetricConnection

namespace TwoAxisHelicoid
open Complex Real Set
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- Construct actual geodesics for the induced metric of a holomorphic
height-normalized end. The connection is extended only to run the ODE;
the resulting curve remains where it is the original connection. -/
theorem holomorphic_height_end_unit_geodesic
    {W : ℂ → ℂ} {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hW : ∀ z : ℂ, R < ‖z‖ → AnalyticAt ℂ W z)
    (hbound : ∀ z : ℂ, R < ‖z‖ → ‖deriv W z‖ ≤ L)
    (z₀ v₀ : ℂ) (hfar : R+4 < ‖z₀‖)
    (hunit : (Real.cosh (W z₀).re)^2*Complex.normSq v₀ = 1) :
    ∃ z v : ℝ → ℂ, z 0 = z₀ ∧ v 0 = v₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        R+2 < ‖z t‖ ∧ HasDerivAt z (v t) t ∧
        HasDerivAt v (-(logGaussConnection W (z t)*(v t)^2)) t ∧
        (Real.cosh (W (z t)).re)^2*Complex.normSq (v t) = 1 ∧ ‖v t‖ ≤ 1 := by
  obtain ⟨Γ,hΓ,hΓb,heq⟩ := bounded_smooth_exterior_extension hR hL
    (fun z hz => logGaussConnection_contDiffAt (hW z hz))
    (fun z hz => (logGaussConnection_norm_le W z).trans (hbound z hz))
  have hr (z : ℂ) (hz : R+2 < ‖z‖) : R < ‖z‖ := by linarith
  obtain ⟨z,v,hz0,hv0,hseg⟩ := exterior_conformal_metric_unit_geodesic
    (φ := logCoshMetric W) (Γ := Γ) (R := R+2)
    (fun z hz => (logCoshMetric_connection (hW z (hr z hz)).differentiableAt.hasDerivAt).1)
    (fun z _ => logCoshMetric_nonneg W z)
    (hΓ.of_le (by simp))
    (fun z hz w => by
      rw [heq z hz.le]
      exact (logCoshMetric_connection (hW z (hr z hz)).differentiableAt.hasDerivAt).2 w)
    hL hΓb z₀ v₀ (by linarith) (by rwa [logCoshMetric_energy])
  refine ⟨z,v,hz0,hv0,?_⟩
  intro t ht
  obtain ⟨hzt,hz,hv,hE,hvnorm⟩ := hseg t ht
  refine ⟨hzt,hz,?_,?_,hvnorm⟩
  · simpa only [heq (z t) hzt.le] using hv
  · simpa only [logCoshMetric_energy] using hE

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.holomorphic_height_end_unit_geodesic
