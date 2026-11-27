import TwoAxisHelicoid.HalfPeriodPositiveSeries
import TwoAxisHelicoid.VerticalEndpoint

namespace TwoAxisHelicoid

/-- The arithmetic coefficient used in the finite endpoint certificates equals
the coefficient of the half-period Fourier expansion at the same positive index. -/
theorem halfPeriodPositiveCoefficient_eq_fourierCoefficientAt {n : ℕ} (hn : 0 < n) :
    halfPeriodPositiveCoefficient n = (fourierCoefficientAt n : ℝ) := by
  let k := n.factorization 2
  let r := n / 2^k
  have odd : Odd r := by
    apply Nat.not_even_iff_odd.mp
    rintro ⟨j, hj⟩
    apply fourier_odd_part_not_two_dvd hn
    exact ⟨j, by change r = 2*j; simpa only [two_mul] using hj⟩
  have decomp : 2^k*r = n := fourier_index_decomposition n
  have formula := halfPeriodPositiveCoefficient_two_power k odd
  rw [decomp] at formula
  change halfPeriodPositiveCoefficient n = (fourierCoefficient k r : ℝ)
  rw [formula]
  by_cases hk : k = 0
  · simp [fourierCoefficient,hk]
  · have hpow : (2:ℕ)^2 ≤ 2^(k+1) := pow_le_pow_right' (by norm_num) (by omega)
    have hsub : 3 ≤ (2:ℕ)^(k+1) := (by norm_num : 3 ≤ (2:ℕ)^2).trans hpow
    simp [fourierCoefficient,hk,Nat.cast_sub hsub]

theorem halfPeriodPositiveCoefficient_complex_eq_fourierCoefficientAt {n : ℕ} (hn : 0 < n) :
    (halfPeriodPositiveCoefficient n : ℂ) = (fourierCoefficientAt n : ℂ) := by
  simpa using congrArg (fun x : ℝ => (x : ℂ)) (halfPeriodPositiveCoefficient_eq_fourierCoefficientAt hn)

/-- On the entire positive parameter axis the analytic F equals the endpoint
certificate's series, including its factor of π² and its constant term. -/
theorem ellipticFReal_eq_verticalSeries {t : ℝ} (ht : 0 < t) :
    ellipticFReal t = verticalSeries t := by
  let q := Real.exp (-Real.pi*t)
  have coeffs : (∑' n : ℕ, halfPeriodPositiveCoefficient (n+1)*q^(n+1)) = qSeries q := by
    unfold qSeries
    apply tsum_congr
    intro n
    rw [halfPeriodPositiveCoefficient_eq_fourierCoefficientAt (Nat.succ_pos n)]
  rw [ellipticFReal_positive_coefficient_series ht,verticalSeries_eq_qSeries]
  change Real.pi^2/4-2*Real.pi^2*(∑' n : ℕ, halfPeriodPositiveCoefficient (n+1)*q^(n+1)) =
    Real.pi^2*(1/4-2*qSeries q)
  rw [coeffs]
  ring

/-- Both strict normalized enclosures and the two signs displayed in §5.3. -/
theorem manuscript_ellipticF_endpoint_enclosures :
    ((-48/10^10 : ℝ) < ellipticFReal (70945978/100000000)/Real.pi^2 ∧
      ellipticFReal (70945978/100000000)/Real.pi^2 < -47/10^10 ∧ (-47/10^10:ℝ) < 0) ∧
    (0 < (139/10^10:ℝ) ∧ (139/10^10:ℝ) < ellipticFReal (70945980/100000000)/Real.pi^2 ∧
      ellipticFReal (70945980/100000000)/Real.pi^2 < 140/10^10) := by
  rw [ellipticFReal_eq_verticalSeries (by norm_num : (0:ℝ) < 70945978/100000000),
    ellipticFReal_eq_verticalSeries (by norm_num : (0:ℝ) < 70945980/100000000)]
  exact ⟨⟨vertical_left_endpoint_normalized.1,vertical_left_endpoint_normalized.2,by norm_num⟩,
    ⟨by norm_num,vertical_right_endpoint_normalized⟩⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.halfPeriodPositiveCoefficient_eq_fourierCoefficientAt
#print axioms TwoAxisHelicoid.halfPeriodPositiveCoefficient_complex_eq_fourierCoefficientAt
#print axioms TwoAxisHelicoid.ellipticFReal_eq_verticalSeries
#print axioms TwoAxisHelicoid.manuscript_ellipticF_endpoint_enclosures
