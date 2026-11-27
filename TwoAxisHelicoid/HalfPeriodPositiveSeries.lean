import TwoAxisHelicoid.HalfPeriodFourier
import TwoAxisHelicoid.HalfPeriodCoefficientArithmetic

namespace TwoAxisHelicoid
open ArithmeticFunction

 theorem sigma_one_power_series_summable {q : ℝ} (hq : |q| < 1) :
    Summable (fun n : ℕ => (sigma 1 n : ℝ)*q^n) := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one 2 (by simpa using hq : ‖q‖ < 1))
  intro n
  have hb : (sigma 1 n : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast sigma_le_pow_succ 1 n
  calc ‖(sigma 1 n : ℝ)*q^n‖ = (sigma 1 n : ℝ)*‖q^n‖ := by
         rw [norm_mul,Real.norm_of_nonneg (by positivity)]
       _ ≤ (n : ℝ)^2*‖q^n‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
       _ = ‖(n : ℝ)^2*q^n‖ := by rw [norm_mul,Real.norm_of_nonneg (sq_nonneg _)]

theorem even_sigma_series {q : ℝ} (hq : |q| < 1) :
    Summable (fun n : ℕ => if Even n then (sigma 1 (n/2) : ℝ)*q^n else 0) ∧
    (∑' n : ℕ, if Even n then (sigma 1 (n/2) : ℝ)*q^n else 0) =
      ∑' n : ℕ, (sigma 1 n : ℝ)*(q^2)^n := by
  let f : ℕ → ℝ := fun n => if Even n then (sigma 1 (n/2) : ℝ)*q^n else 0
  have hq2 : |q^2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg q) hq (by decide : 2 ≠ 0)
  have he (n : ℕ) : f (2*n) = (sigma 1 n : ℝ)*(q^2)^n := by
    have hn : Even (2*n) := ⟨n,by omega⟩
    have hd : 2*n/2 = n := by omega
    simp only [f,ite_eq_left hn,hd,pow_mul]
  have ho (n : ℕ) : f (2*n+1) = 0 := by
    have hn : ¬ Even (2*n+1) := Nat.not_even_iff_odd.mpr ⟨n,rfl⟩
    simp [f,hn]
  have hse : Summable (fun n => f (2*n)) :=
    (sigma_one_power_series_summable hq2).congr (fun n => (he n).symm)
  have hso : Summable (fun n => f (2*n+1)) := by simp_rw [ho]; exact summable_zero
  refine ⟨hse.even_add_odd hso,?_⟩
  change (∑' n, f n) = _
  rw [← tsum_even_add_odd hse hso,tsum_congr he,tsum_congr ho,tsum_zero,add_zero]

theorem halfPeriodPositiveCoefficient_series {q : ℝ} (hq : |q| < 1) :
    Summable (fun n : ℕ => halfPeriodPositiveCoefficient n*q^n) ∧
    (∑' n : ℕ, halfPeriodPositiveCoefficient n*q^n) =
      4*(∑' n : ℕ, (sigma 1 n : ℝ)*(q^2)^n)-
        (∑' n : ℕ, (sigma 1 n : ℝ)*(-q)^n) := by
  obtain ⟨he,hse⟩ := even_sigma_series hq
  have hs := sigma_one_power_series_summable (show |-q| < 1 by simpa using hq)
  have hid (n : ℕ) : halfPeriodPositiveCoefficient n*q^n =
      4*(if Even n then (sigma 1 (n/2) : ℝ)*q^n else 0)-(sigma 1 n : ℝ)*(-q)^n := by
    by_cases hn : Even n
    · rw [halfPeriodPositiveCoefficient,ite_eq_left hn,ite_eq_left hn,hn.neg_pow]
      ring
    · have ho := Nat.not_even_iff_odd.mp hn
      rw [halfPeriodPositiveCoefficient,ite_eq_right hn,ite_eq_right hn,ho.neg_pow]
      ring
  have hsum := (he.mul_left 4).sub hs
  refine ⟨hsum.congr (fun n => (hid n).symm),?_⟩
  rw [tsum_congr hid,(he.mul_left 4).tsum_sub hs,tsum_mul_left,hse]

/-- The actual elliptic function has exactly the manuscript's positive
coefficient Fourier expansion. Convergence and the 2-adic arithmetic
formula are both proved independently of the numerical certificates. -/
theorem ellipticFReal_positive_coefficient_series {t : ℝ} (ht : 0 < t) :
    ellipticFReal t = Real.pi^2/4-2*Real.pi^2*
      (∑' n : ℕ, halfPeriodPositiveCoefficient (n+1)*(Real.exp (-Real.pi*t))^(n+1)) := by
  let q := Real.exp (-Real.pi*t)
  have hq : |q| < 1 := by
    dsimp [q]
    rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ht
  have hq2 : |q^2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg q) hq (by decide : 2 ≠ 0)
  have hshift {r : ℝ} (hr : |r| < 1) :
      (∑' n : ℕ, (sigma 1 n : ℝ)*r^n) =
        ∑' n : ℕ, (sigma 1 (n+1) : ℝ)*r^(n+1) := by
    rw [(sigma_one_power_series_summable hr).tsum_eq_zero_add]
    simp
  obtain ⟨hb,heb⟩ := halfPeriodPositiveCoefficient_series hq
  have hbshift : (∑' n : ℕ, halfPeriodPositiveCoefficient n*q^n) =
      ∑' n : ℕ, halfPeriodPositiveCoefficient (n+1)*q^(n+1) := by
    rw [hb.tsum_eq_zero_add]
    simp [halfPeriodPositiveCoefficient]
  have hf := ellipticFReal_sigma_series ht
  change ellipticFReal t = Real.pi^2 * (1/4+
    2*(∑' n : ℕ, (sigma 1 (n+1) : ℝ)*(-q)^(n+1))-
    8*(∑' n : ℕ, (sigma 1 (n+1) : ℝ)*((-q)^2)^(n+1))) at hf
  rw [neg_sq,← hshift hq2,← hshift (show |-q| < 1 by simpa using hq)] at hf
  change ellipticFReal t = Real.pi^2/4-2*Real.pi^2*
    (∑' n : ℕ, halfPeriodPositiveCoefficient (n+1)*q^(n+1))
  rw [← hbshift,heb,hf]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_positive_coefficient_series
