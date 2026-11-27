import TwoAxisHelicoid.CompactChartHarmonic

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem analytic_deriv_zero_of_locally_constant_re {F : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z)
    (hr : ∀ᶠ w in 𝓝 z, (F w).re = (F z).re) : deriv F z = 0 := by
  have hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun v => exp (F v)) w := by
    filter_upwards [hF.eventually_analyticAt] with w hw
    exact hw.differentiableAt.cexp
  have hm : IsLocalMax (norm ∘ fun w => exp (F w)) z := by
    filter_upwards [hr] with w hw
    simp only [Function.comp_def,Complex.norm_exp,hw,le_refl]
  have hc := Complex.eventually_eq_of_isLocalMax_norm hd hm
  have h0 := (hasDerivAt_const z (exp (F z))).congr_of_eventuallyEq hc
  have he := hF.differentiableAt.hasDerivAt.cexp.unique h0
  exact (mul_eq_zero.mp he).resolve_left (Complex.exp_ne_zero _)

/-- The local holomorphic coefficient of a global real harmonic primitive
vanishes on a compact connected complex charted space. Constructing that
primitive from zero real periods is a separate obligation. -/
theorem compact_real_primitive_holomorphic_coefficient_zero {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X] [PreconnectedSpace X]
    {u : X → ℝ} (hu : Continuous u) (hh : HarmonicInComplexCharts u)
    (p : X) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F (chartAt ℂ p p))
    (hRe : ∀ᶠ z in 𝓝 (chartAt ℂ p p), (F z).re = u ((chartAt ℂ p).symm z)) :
    deriv F (chartAt ℂ p p) = 0 := by
  have hc := compact_connected_chart_harmonic_constant hu hh
  apply analytic_deriv_zero_of_locally_constant_re hF
  filter_upwards [hRe] with z hz
  exact hz.trans ((hc _ _).trans hRe.self_of_nhds.symm)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_real_primitive_holomorphic_coefficient_zero
