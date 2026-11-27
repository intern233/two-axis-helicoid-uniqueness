import TwoAxisHelicoid.EllipticFFourierRayTransfer

namespace TwoAxisHelicoid
open Filter Set
open scoped Topology

/-- The order-`k` derivative of the `n+1` summand in the positive-coefficient
expansion of the elliptic half-period function, before its factor `-2π²`. -/
noncomputable def halfPeriodExponentialTerm (k n : ℕ) (t : ℝ) : ℝ :=
  let frequency := -Real.pi * ((n+1 : ℕ) : ℝ)
  halfPeriodPositiveCoefficient (n+1) * frequency^k * Real.exp (frequency*t)

/-- Ordinary partial sums of the order-`k` differentiated Fourier series
converge uniformly on every `[a,∞)` with `a>0`, hence on every compact
subinterval of the original parameter axis. -/
theorem halfPeriod_derivative_series_uniform (k : ℕ) {a : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn
      (fun N t => ∑ n ∈ Finset.range N, halfPeriodExponentialTerm k n t)
      (fun t => ∑' n, halfPeriodExponentialTerm k n t) atTop (Ici a) :=
  (ellipticFReal_fourier_derivatives_on_rays k).1 a ha

/-- For every positive order, the actual function F has the termwise
derivative of its Fourier series on the full open parameter axis. -/
theorem ellipticFReal_all_positive_order_derivatives (k : ℕ) (hk : 0 < k)
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv k ellipticFReal t = -(2*Real.pi^2 * ∑' n, halfPeriodExponentialTerm k n t) :=
  (ellipticFReal_fourier_derivatives_on_rays k).2 t ht hk

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.halfPeriod_derivative_series_uniform
#print axioms TwoAxisHelicoid.ellipticFReal_all_positive_order_derivatives
