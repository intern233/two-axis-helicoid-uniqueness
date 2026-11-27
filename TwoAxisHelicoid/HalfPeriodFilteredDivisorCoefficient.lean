import TwoAxisHelicoid.HalfPeriodPositiveSeries

namespace TwoAxisHelicoid
open ArithmeticFunction Finset

/-- The second Lambert numerator has exponents 2d,4d,…. It contributes
no divisors at an odd exponent; at an even exponent n its divisors are
those of n/2. -/
noncomputable def signedLambertDivisorCoefficient (n : ℕ) : ℝ :=
  (∑ d ∈ n.divisors with Odd (n/d), (d:ℝ)*(-1:ℝ)^d) -
    3*(if Even n then ∑ d ∈ (n/2).divisors, (d:ℝ) else 0)

private theorem real_sum_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (d:ℝ)) = (sigma 1 n : ℝ) := by
  rw [sigma_one_apply,Nat.cast_sum]

private theorem odd_quotient_sum_at_odd {n : ℕ} (hn : Odd n) :
    (∑ d ∈ n.divisors with Odd (n/d), (d:ℝ)*(-1:ℝ)^d) = -(sigma 1 n : ℝ) := by
  have parts (d : ℕ) (hd : d ∈ n.divisors) : Odd d ∧ Odd (n/d) := by
    apply Nat.odd_mul.mp
    rwa [Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
  rw [Finset.filter_true_of_mem (fun d hd => (parts d hd).2)]
  calc
    _ = ∑ d ∈ n.divisors, -(d:ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [(parts d hd).1.neg_one_pow,mul_neg_one]
    _ = _ := by rw [Finset.sum_neg_distrib,real_sum_divisors]

private theorem odd_quotient_sum_at_even {m : ℕ} (hm : 0 < m) :
    (∑ d ∈ (2*m).divisors with Odd (2*m/d), (d:ℝ)*(-1:ℝ)^d) =
      (sigma 1 (2*m) : ℝ)-(sigma 1 m : ℝ) := by
  have parity : Even (2*m) := ⟨m,by omega⟩
  have half {d : ℕ} (dvd : d ∣ 2*m) : ¬Odd (2*m/d) ↔ d ∣ m := by
    rw [Nat.not_odd_iff_even,even_iff_two_dvd,Nat.dvd_div_iff_mul_dvd dvd]
    simp only [Nat.mul_comm d 2,Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)]
  have complement : (2*m).divisors.filter (fun d => ¬Odd (2*m/d)) = m.divisors := by
    ext d
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨mem,he⟩
      exact Nat.mem_divisors.mpr ⟨(half (Nat.mem_divisors.mp mem).1).mp he,hm.ne'⟩
    · intro mem
      have dvd := (Nat.mem_divisors.mp mem).1
      have dvd2 : d ∣ 2*m := dvd.trans (dvd_mul_left m 2)
      exact ⟨Nat.mem_divisors.mpr ⟨dvd2,by positivity⟩,(half dvd2).mpr dvd⟩
  have rel := Finset.sum_filter_add_sum_filter_not (2*m).divisors (fun d => Odd (2*m/d)) (fun d => (d:ℝ))
  rw [complement] at rel
  simp only [real_sum_divisors] at rel
  calc
    _ = ∑ d ∈ (2*m).divisors with Odd (2*m/d), (d:ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨mem,ho⟩ := Finset.mem_filter.mp hd
      have both : Even (d*(2*m/d)) := by
        rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp mem).1]
        exact parity
      have ed := (Nat.even_mul.mp both).resolve_right (Nat.not_even_iff_odd.mpr ho)
      rw [ed.neg_one_pow,mul_one]
    _ = _ := by linarith only [rel]

/-- The finite sum at manuscript line 767 gives the negative of the
coefficient in the already identified positive Fourier series. -/
theorem signedLambertDivisorCoefficient_eq_neg {n : ℕ} (hn : 0 < n) :
    signedLambertDivisorCoefficient n = -halfPeriodPositiveCoefficient n := by
  by_cases he : Even n
  · have eq : n = 2*(n/2) := by obtain ⟨j,hj⟩ := he; omega
    have half := odd_quotient_sum_at_even (m := n/2) (by omega)
    rw [← eq] at half
    rw [signedLambertDivisorCoefficient,ite_eq_left he,half,real_sum_divisors,
      halfPeriodPositiveCoefficient,ite_eq_left he]
    ring
  · have ho := Nat.not_even_iff_odd.mp he
    rw [signedLambertDivisorCoefficient,ite_eq_right he,odd_quotient_sum_at_odd ho,
      halfPeriodPositiveCoefficient_odd ho]
    ring

theorem signedLambertDivisorCoefficient_two_power (k : ℕ) {r : ℕ} (hr : Odd r) :
    signedLambertDivisorCoefficient (2^k*r) =
      -(if k = 0 then (sigma 1 r : ℝ) else ((2:ℝ)^(k+1)-3)*(sigma 1 r : ℝ)) := by
  have rp : 0 < r := by
    obtain ⟨j,hj⟩ := hr
    omega
  rw [signedLambertDivisorCoefficient_eq_neg (by positivity),halfPeriodPositiveCoefficient_two_power k hr]

/-- The actual half-period function as the series of these signed,
odd-quotient-filtered divisor sums. -/
theorem ellipticFReal_filtered_divisor_series {t : ℝ} (ht : 0 < t) :
    ellipticFReal t = Real.pi^2/4+2*Real.pi^2*
      (∑' n : ℕ, signedLambertDivisorCoefficient (n+1)*(Real.exp (-Real.pi*t))^(n+1)) := by
  let q := Real.exp (-Real.pi*t)
  have changeSign : (∑' n : ℕ, signedLambertDivisorCoefficient (n+1)*q^(n+1)) =
      -(∑' n : ℕ, halfPeriodPositiveCoefficient (n+1)*q^(n+1)) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro n
    rw [signedLambertDivisorCoefficient_eq_neg (Nat.succ_pos n),neg_mul]
  rw [ellipticFReal_positive_coefficient_series ht]
  change _ = Real.pi^2/4+2*Real.pi^2*(∑' n : ℕ, signedLambertDivisorCoefficient (n+1)*q^(n+1))
  rw [changeSign]
  dsimp only [q]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.signedLambertDivisorCoefficient_eq_neg
#print axioms TwoAxisHelicoid.signedLambertDivisorCoefficient_two_power
#print axioms TwoAxisHelicoid.ellipticFReal_filtered_divisor_series
