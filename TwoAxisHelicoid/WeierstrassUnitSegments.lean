import TwoAxisHelicoid.WeierstrassGeodesicCurve
import TwoAxisHelicoid.HolomorphicEndGeodesic

namespace TwoAxisHelicoid
open Complex Real Set
set_option maxHeartbeats 1000000

/-- Actual surface curves realizing every unit tangent vector on a
height-normalized end. Both the unit spatial speed and the bounded spatial
acceleration are derived from the actual Weierstrass differential. -/
theorem holomorphic_height_end_actual_unit_segments
    {X : ℂ → Fin 3 → ℝ} {W : ℂ → ℂ} {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hW : ∀ z : ℂ, R < ‖z‖ → AnalyticAt ℂ W z)
    (hbound : ∀ z : ℂ, R < ‖z‖ → ‖deriv W z‖ ≤ L)
    (hX : ∀ z : ℂ, R < ‖z‖ →
      HasFDerivAt X (nullRealDerivative (weierstrassTriple (exp (W z)) 1)) z)
    (z₀ v₀ : ℂ) (hfar : R+4 < ‖z₀‖)
    (hunit : (∑ j, (nullRealDerivative (weierstrassTriple (exp (W z₀)) 1) v₀ j)^2) = 1) :
    ∃ γ : ℝ → ℂ, ∃ w a : ℝ → Fin 3 → ℝ,
      γ 0 = z₀ ∧ w 0 = nullRealDerivative (weierstrassTriple (exp (W z₀)) 1) v₀ ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        R+2 < ‖γ t‖ ∧ HasDerivAt (X ∘ γ) (w t) t ∧ HasDerivAt w (a t) t ∧
        (∑ j, (w t j)^2) = 1 ∧ (∑ j, (a t j)^2) ≤ L^2 := by
  rw [weierstrass_exp_direction_metric] at hunit
  obtain ⟨γ,v,hγ0,hv0,hseg⟩ := holomorphic_height_end_unit_geodesic hR hL hW hbound z₀ v₀ hfar hunit
  let w : ℝ → Fin 3 → ℝ := fun t => nullRealDerivative (weierstrassTriple (exp (W (γ t))) 1) (v t)
  let a : ℝ → Fin 3 → ℝ := fun t =>
    -(deriv W (γ t)*(v t)^2).re • logGaussSphere (W (γ t)).re (W (γ t)).im
  refine ⟨γ,w,a,hγ0,by dsimp [w]; rw [hγ0,hv0],?_⟩
  intro t ht
  obtain ⟨hγt,hγ,hv,hE,hvnorm⟩ := hseg t ht
  have hRt : R < ‖γ t‖ := by linarith
  refine ⟨hγt,(hX (γ t) hRt).comp_hasDerivAt t hγ,?_,?_,?_⟩
  · exact weierstrass_geodesic_velocity_hasDerivAt_normal (hW (γ t) hRt).differentiableAt.hasDerivAt hγ hv
  · change (∑ j, (nullRealDerivative (weierstrassTriple (exp (W (γ t))) 1) (v t) j)^2) = 1
    rw [weierstrass_exp_direction_metric]
    exact hE
  · change (∑ j, (-(deriv W (γ t)*(v t)^2).re*logGaussSphere (W (γ t)).re (W (γ t)).im j)^2) ≤ L^2
    exact (weierstrass_geodesic_acceleration_bound (W (γ t)) (deriv W (γ t)) (v t) hvnorm).trans
      (pow_le_pow_left₀ (norm_nonneg _) (hbound (γ t) hRt) 2)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.holomorphic_height_end_actual_unit_segments
