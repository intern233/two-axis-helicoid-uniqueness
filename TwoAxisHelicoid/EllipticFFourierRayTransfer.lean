import TwoAxisHelicoid.PolynomialFourierDerivativeRays
import TwoAxisHelicoid.HalfPeriodPositiveSeries

namespace TwoAxisHelicoid
open Filter Set
open scoped Topology

/-- Uniform convergence of the actual divisor-coefficient terms on every
positive closed ray, together with all positive-order derivatives of F. -/
theorem ellipticFReal_fourier_derivatives_on_rays (k : ℕ) :
    let a := fun n : ℕ => halfPeriodPositiveCoefficient (n+1)
    (∀ p : ℝ, 0 < p → TendstoUniformlyOn
      (fun N t => ∑ n ∈ Finset.range N, polynomialFourierTerm a Real.pi k n t)
      (fun t => ∑' n, polynomialFourierTerm a Real.pi k n t) atTop (Ici p)) ∧
    (∀ t : ℝ, 0 < t → 0 < k → iteratedDeriv k ellipticFReal t =
      -(2 * Real.pi ^ 2 * ∑' n, polynomialFourierTerm a Real.pi k n t)) := by
  let a := fun n : ℕ => halfPeriodPositiveCoefficient (n+1)
  have bounds (n : ℕ) : 0 ≤ a n ∧ a n ≤ ((n+1 : ℕ) : ℝ)^2 := by
    obtain ⟨lo,hi,top⟩ := halfPeriodPositiveCoefficient_bounds (Nat.succ_pos n)
    exact ⟨zero_le_one.trans lo, hi.trans top⟩
  refine ⟨fun _ hp => polynomialFourier_derivatives_uniform a bounds Real.pi_pos hp k, ?_⟩
  intro t ht hk
  let S := fun x : ℝ => ∑' n, polynomialFourierTerm a Real.pi 0 n x
  have germ : ellipticFReal =ᶠ[𝓝 t] (fun x => Real.pi^2/4 - 2*Real.pi^2*S x) := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    rw [ellipticFReal_positive_coefficient_series hx]
    apply congrArg (fun y : ℝ => Real.pi^2/4 - 2*Real.pi^2*y)
    apply tsum_congr
    intro n
    change a n * Real.exp (-Real.pi*x)^(n+1) =
      a n * (-Real.pi*((n+1 : ℕ) : ℝ))^0 * Real.exp ((-Real.pi*((n+1 : ℕ) : ℝ))*x)
    rw [pow_zero, mul_one, ← Real.exp_nat_mul]
    apply congrArg (fun w : ℝ => a n * Real.exp w)
    ring
  rw [germ.iteratedDeriv_eq k, iteratedDeriv_const_sub hk]
  change iteratedDeriv k (fun x => -(2*Real.pi^2*S x)) t = _
  rw [iteratedDeriv_fun_neg, iteratedDeriv_const_mul_field]
  exact congrArg (fun y : ℝ => -(2*Real.pi^2*y))
    (polynomialFourier_sum_iteratedDeriv a bounds Real.pi_pos k ht)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ellipticFReal_fourier_derivatives_on_rays
