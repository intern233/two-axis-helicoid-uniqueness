import TwoAxisHelicoid.PolynomialNomeFourier
import TwoAxisHelicoid.HalfPeriodPositiveSeries
import TwoAxisHelicoid.EllipticFGlobalDerivative

namespace TwoAxisHelicoid
open Filter Set
open scoped Topology

/-- The derivative and both endpoint limits in the manuscript's Fourier display,
for the geometric half-period and its actual divisor coefficients. -/
theorem ellipticFReal_fourier_display_of_polynomial_nome :
    (∀ t : ℝ, 0 < t →
      deriv ellipticFReal t = 2 * Real.pi ^ 3 * ∑' n : ℕ,
        ((n + 1 : ℕ) : ℝ) * halfPeriodPositiveCoefficient (n + 1) *
          Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * t)) ∧
    (∀ t : ℝ, 0 < t → 0 < deriv ellipticFReal t) ∧
    Tendsto ellipticFReal atTop (𝓝 (Real.pi ^ 2 / 4)) ∧
    Tendsto ellipticFReal (𝓝[>] (0 : ℝ)) atBot := by
  let a := fun n : ℕ => halfPeriodPositiveCoefficient (n + 1)
  have bounds (n : ℕ) : 1 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    obtain ⟨lo, hi, top⟩ := halfPeriodPositiveCoefficient_bounds (Nat.succ_pos n)
    exact ⟨lo, hi.trans top⟩
  let S := fun t : ℝ => polynomialNomeSeries a (Real.exp (-Real.pi * t))
  have eqF {t : ℝ} (ht : 0 < t) : ellipticFReal t = Real.pi ^ 2 / 4 - 2 * Real.pi ^ 2 * S t :=
    ellipticFReal_positive_coefficient_series ht
  obtain ⟨far, near⟩ := polynomialNome_exponential_limits a bounds Real.pi_pos
  have hp : 0 < 2 * Real.pi ^ 2 := by positivity
  refine ⟨?_, fun _ h => ellipticFReal_deriv_pos_of_pos h, ?_, ?_⟩
  · intro t ht
    have d := polynomialNome_exponential_hasDerivAt a
      (fun n => ⟨zero_le_one.trans (bounds n).1, (bounds n).2⟩) Real.pi_pos ht
    have germ : ellipticFReal =ᶠ[𝓝 t] (fun y => Real.pi ^ 2 / 4 - 2 * Real.pi ^ 2 * S y) :=
      (eventually_gt_nhds ht).mono fun _ hy => eqF hy
    rw [(((d.const_mul (2 * Real.pi ^ 2)).const_sub (Real.pi ^ 2 / 4)).congr_of_eventuallyEq germ).deriv]
    change -(2 * Real.pi ^ 2 * (-Real.pi * _)) = 2 * Real.pi ^ 3 * _
    ring
  · have lim := (tendsto_const_nhds (x := Real.pi ^ 2 / 4)).sub (far.const_mul (2 * Real.pi ^ 2))
    rw [mul_zero, sub_zero] at lim
    exact lim.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun _ ht => (eqF ht).symm)
  · apply tendsto_atBot.mpr
    intro B
    have crossed := (tendsto_atTop.mp near) ((Real.pi ^ 2 / 4 - B) / (2 * Real.pi ^ 2))
    filter_upwards [crossed, self_mem_nhdsWithin] with t h pos
    rw [eqF pos]
    have inequality := (div_le_iff₀ hp).mp h
    change Real.pi ^ 2 / 4 - B ≤ S t * (2 * Real.pi ^ 2) at inequality
    linarith only [inequality]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_fourier_display_of_polynomial_nome
