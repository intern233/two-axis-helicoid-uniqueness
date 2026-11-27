import TwoAxisHelicoid.LogarithmicCuspMetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

namespace TwoAxisHelicoid
open Real Complex Set MeasureTheory Filter
open scoped Topology

/-- A differentiable curve tending to infinity at the boundary of a
finite interval has infinite length in the logarithmic cusp metric. -/
theorem escaping_curve_cusp_speed_not_integrable {γ : ℝ → ℂ}
    (diff : ∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ γ t)
    (outside : ∀ t ∈ Ioo (0:ℝ) 1, 2 < ‖γ t‖)
    (escape : Tendsto (fun t => ‖γ t‖) (𝓝[<] 1) atTop) :
    ¬ IntegrableOn (fun t => exteriorCuspDensity ‖γ t‖ * ‖deriv γ t‖) (Ioo (0:ℝ) 1) := by
  let B := fun t => exteriorCuspDensity ‖γ t‖ * ‖deriv γ t‖
  let φ := fun t => Real.log (Real.log ‖γ t‖)
  have nonneg (t : ℝ) : 0 ≤ B t := mul_nonneg (exteriorCuspDensity_nonneg _) (norm_nonneg _)
  have chain (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      DifferentiableAt ℝ φ t ∧ ‖deriv φ t‖ ≤ B t := by
    obtain ⟨d, bound⟩ := loglog_radius_derivative_bound (outside t ht) (deriv γ t)
    have c := d.hasFDerivAt.comp_hasDerivAt t (diff t ht).hasDerivAt
    refine ⟨c.differentiableAt,?_⟩
    have val : deriv φ t = fderiv ℝ (fun w : ℂ => Real.log (Real.log ‖w‖)) (γ t) (deriv γ t) := c.deriv
    rw [val,Real.norm_eq_abs]
    exact bound
  intro integrable
  change IntegrableOn B (Ioo (0:ℝ) 1) at integrable
  have estimate (x : ℝ) (hx : x ∈ Ioo (1/2:ℝ) 1) :
      φ x ≤ φ (1/2) + ∫ t in Ioo (0:ℝ) 1, B t := by
    have sub : Icc (1/2:ℝ) x ⊆ Ioo (0:ℝ) 1 := fun t ht =>
      ⟨lt_of_lt_of_le (by norm_num) ht.1, ht.2.trans_lt hx.2⟩
    have io : Ioc (1/2:ℝ) x ⊆ Ioo (0:ℝ) 1 := Ioc_subset_Icc_self.trans sub
    have bound := norm_sub_le_integral_of_norm_deriv_le_of_le (f := φ) (B := B) hx.1.le
      (fun t ht => (chain t (sub ht)).1.continuousAt.continuousWithinAt)
      (fun t ht => (chain t (sub (Ioo_subset_Icc_self ht))).1.differentiableWithinAt)
      (.of_forall fun t ht => (chain t (sub (Ioo_subset_Icc_self ht))).2)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1.le).mpr (integrable.mono_set io))
    rw [intervalIntegral.integral_of_le hx.1.le,Real.norm_eq_abs] at bound
    have upper := setIntegral_mono_set integrable (Filter.Eventually.of_forall nonneg)
      (Filter.Eventually.of_forall io)
    linarith [le_abs_self (φ x - φ (1/2))]
  have tend : Tendsto φ (𝓝[<] 1) atTop := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp escape)
  have near : ∀ᶠ x : ℝ in 𝓝[<] 1, x∈Ioo (1/2:ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  obtain ⟨x, hx, h⟩ := (near.and (tend.eventually_gt_atTop (φ (1/2) + ∫ t in Ioo (0:ℝ) 1, B t))).exists
  exact (estimate x hx).not_gt h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.escaping_curve_cusp_speed_not_integrable
