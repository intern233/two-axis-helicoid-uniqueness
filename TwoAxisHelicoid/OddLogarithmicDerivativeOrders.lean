module

public import TwoAxisHelicoid.OddLogarithmicDerivativeGerm
public import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section
namespace TwoAxisHelicoid
open Filter Asymptotics
open scoped Topology

/-- The two remainder orders at the origin can be read directly from the
zero divisor and the differential equation away from it. -/
theorem odd_logarithmic_derivative_orders_of_divisor {f g : ℂ → ℂ} {P : ℂ → Prop}
    (analytic : AnalyticAt ℂ f 0) (odd : ∀ z, f (-z) = -f z)
    (tangent : HasDerivAt f 1 0) (third : iteratedDeriv 3 f 0 = 0)
    (zeros : ∀ z, f z = 0 ↔ P z)
    (equation : ∀ {z}, ¬P z → HasDerivAt f (g z * f z) z) :
    ((fun z : ℂ => f z - z) =O[𝓝 0] (fun z => z^5)) ∧
    ((fun z : ℂ => g z - z⁻¹) =O[𝓝[≠] 0] (fun z => z^3)) := by
  obtain ⟨A, B, ha, hb, first, second⟩ :=
    odd_logarithmic_derivative_origin_factors analytic odd tangent.deriv third
      (fun z h => (equation (fun hz => h ((zeros z).mpr hz))).deriv)
  have bound {l : Filter ℂ} {u v w : ℂ → ℂ} (h : Tendsto w l (𝓝 (w 0)))
      (factor : ∀ᶠ z in l, u z = v z * w z) : u =O[l] v := by
    apply isBigO_iff.mpr
    refine ⟨‖w 0‖+1, ?_⟩
    have bounded := h.norm.eventually_lt_const (show ‖w 0‖ < ‖w 0‖+1 by linarith)
    filter_upwards [factor, bounded] with z hz hw
    rw [hz, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hw.le (norm_nonneg _)
  exact ⟨bound ha.continuousAt.tendsto (first.mono fun z h => by rw [h]; ring),
    bound (hb.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (second.mono fun z h => by rw [h]; ring)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.odd_logarithmic_derivative_orders_of_divisor
