import TwoAxisHelicoid.EllipticFNomeFourierTransfer

namespace TwoAxisHelicoid
open Filter Set
open scoped Topology

/-- The actual derivative in the positive-coefficient expansion of §5.
The index n+1 ranges over all positive integers. -/
theorem ellipticFReal_hasDerivAt_positive_series {t : ℝ} (ht : 0 < t) :
    HasDerivAt ellipticFReal (2*Real.pi^3*
      ∑' n : ℕ, ((n+1:ℕ):ℝ)*halfPeriodPositiveCoefficient (n+1)*
        Real.exp (-Real.pi*((n+1:ℕ):ℝ)*t)) t := by
  rw [← ellipticFReal_fourier_display_of_polynomial_nome.1 t ht]
  exact (ellipticFReal_differentiableAt ht).hasDerivAt

/-- Both endpoint limits from the same positive series. At the left
endpoint its first N terms already dominate a sum tending to N. -/
theorem ellipticFReal_limits_from_positive_series :
    Tendsto ellipticFReal atTop (𝓝 (Real.pi^2/4)) ∧
    Tendsto ellipticFReal (𝓝[>] (0:ℝ)) atBot :=
  ellipticFReal_fourier_display_of_polynomial_nome.2.2

/-- The three assertions in the display opening at manuscript line 779. -/
theorem ellipticFReal_positive_fourier_display :
    (∀ t : ℝ, 0 < t →
      deriv ellipticFReal t = 2*Real.pi^3*(∑' n : ℕ,
        ((n+1:ℕ):ℝ)*halfPeriodPositiveCoefficient (n+1)*Real.exp (-Real.pi*((n+1:ℕ):ℝ)*t)) ∧
      0 < deriv ellipticFReal t) ∧ Tendsto ellipticFReal atTop (𝓝 (Real.pi^2/4)) ∧
      Tendsto ellipticFReal (𝓝[>] (0:ℝ)) atBot :=
  ⟨fun _ ht => ⟨(ellipticFReal_hasDerivAt_positive_series ht).deriv,ellipticFReal_deriv_pos_of_pos ht⟩,
    ellipticFReal_limits_from_positive_series⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_hasDerivAt_positive_series
#print axioms TwoAxisHelicoid.ellipticFReal_limits_from_positive_series
#print axioms TwoAxisHelicoid.ellipticFReal_positive_fourier_display
