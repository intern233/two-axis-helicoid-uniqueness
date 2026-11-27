module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace TwoAxisHelicoid
open Filter Set
open scoped Topology

/-- The positive-power series indexed by the frequency (n+1). -/
noncomputable def polynomialNomeSeries (a : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑' n : ℕ, a n * q ^ (n + 1)

private theorem cubic_nome_majorant {R : ℝ} (hr : 0 < R) (hR : ‖R‖ < 1) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 3 * R ^ n) := by
  let polynomial := fun n : ℕ => (n : ℝ) ^ 3 * R ^ n
  have at_zero : Summable polynomial := summable_pow_mul_geometric_of_norm_lt_one 3 hR
  have base : Summable (fun n : ℕ => polynomial (n + 1)) :=
    (summable_nat_add_iff (f := polynomial) 1).mpr at_zero
  apply (base.mul_right R⁻¹).congr
  intro n
  change (((n + 1 : ℕ) : ℝ) ^ 3 * R ^ (n + 1)) * R⁻¹ = _
  rw [pow_succ R n, mul_assoc, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one]

private theorem nome_monomial_deriv (a : ℕ → ℝ) (n : ℕ) (q : ℝ) :
    HasDerivAt (fun x : ℝ => a n * x ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * a n * q ^ n) q := by
  convert (hasDerivAt_pow (n + 1) q).const_mul (a n) using 1
  simp
  ring

private theorem nome_monomial_bound (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    (n : ℕ) {x R : ℝ} (hx : x ∈ Ioo (-R) R) :
    ‖((n + 1 : ℕ) : ℝ) * a n * x ^ n‖ ≤ ((n + 1 : ℕ) : ℝ) ^ 3 * R ^ n := by
  have hn : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hprod : ((n + 1 : ℕ) : ℝ) * a n ≤ ((n + 1 : ℕ) : ℝ) ^ 3 :=
    (mul_le_mul_of_nonneg_left (ha n).2 hn).trans_eq (by ring)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hn (ha n).1), abs_pow]
  exact mul_le_mul hprod (pow_le_pow_left₀ (abs_nonneg x) (abs_lt.mpr hx).le n)
    (pow_nonneg (abs_nonneg x) n) (pow_nonneg hn 3)

/-- Termwise differentiation throughout the open interval of convergence,
with the summable cubic majorant obtained from the quadratic coefficient bound. -/
theorem polynomialNomeSeries_hasDerivAt (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    {q : ℝ} (hq : |q| < 1) :
    HasDerivAt (polynomialNomeSeries a)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * a n * q ^ n) q := by
  let R := (|q| + 1) / 2
  have qr : |q| < R := by dsimp [R]; linarith
  have rp := (abs_nonneg q).trans_lt qr
  have r1 : ‖R‖ < 1 := by rw [Real.norm_of_nonneg rp.le]; dsimp [R]; linarith
  change HasDerivAt (fun y : ℝ => ∑' n : ℕ, a n * y ^ (n + 1)) _ q
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun n x => a n * x ^ (n + 1))
    (g' := fun n x => ((n + 1 : ℕ) : ℝ) * a n * x ^ n)
    (t := Ioo (-R) R) (y₀ := 0) (y := q) (cubic_nome_majorant rp r1)
    isOpen_Ioo isPreconnected_Ioo
  · exact fun n x _ => nome_monomial_deriv a n x
  · exact fun n x hx => nome_monomial_bound a ha n hx
  · exact ⟨neg_lt_zero.mpr rp, rp⟩
  · simp
  · exact abs_lt.mp qr

/-- Real Fourier differentiation after substituting (q=exp(-ct)) at any
positive frequency scale and any positive parameter. -/
theorem polynomialNome_exponential_hasDerivAt (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => polynomialNomeSeries a (Real.exp (-c * x)))
      (-c * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * a n * Real.exp (-c * ((n + 1 : ℕ) : ℝ) * t)) t := by
  let q := Real.exp (-c * t)
  have hq : |q| < 1 := by
    dsimp only [q]
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc) ht
  have dq : HasDerivAt (fun x : ℝ => Real.exp (-c * x)) (-c * q) t := by
    convert ((hasDerivAt_id t).const_mul (-c)).exp using 1 <;> simp [q]
    ring
  have hd := (polynomialNomeSeries_hasDerivAt a ha hq).comp t dq
  have shift : (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * a n * q ^ n) * q =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * a n * Real.exp (-c * ((n + 1 : ℕ) : ℝ) * t) := by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro n
    have power : Real.exp (-c * ((n + 1 : ℕ) : ℝ) * t) = q ^ (n + 1) := by
      dsimp only [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [power, pow_succ]
    ring
  rw [← shift, mul_left_comm (-c) _ q]
  exact hd

private theorem polynomial_nome_summable (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    {q : ℝ} (hq : 0 ≤ q) (q1 : q < 1) :
    Summable (fun n : ℕ => a n * q ^ (n + 1)) := by
  have radius : ‖q‖ < 1 := by rwa [Real.norm_of_nonneg hq]
  apply Summable.of_norm_bounded ((summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ 2 * q ^ n) 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one 2 radius))
  intro n
  rw [Real.norm_of_nonneg (mul_nonneg (ha n).1 (pow_nonneg hq _))]
  exact mul_le_mul_of_nonneg_right (ha n).2 (pow_nonneg hq _)

/-- A positive integer-frequency series with coefficients between one and
the squared frequency vanishes at infinity and diverges at the positive side
of zero. The small-parameter estimate already holds on every finite prefix. -/
theorem polynomialNome_exponential_limits (a : ℕ → ℝ)
    (ha : ∀ n, 1 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => polynomialNomeSeries a (Real.exp (-c * t))) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => polynomialNomeSeries a (Real.exp (-c * t))) (𝓝[>] 0) atTop := by
  have bounds (n : ℕ) : 0 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2 :=
    ⟨zero_le_one.trans (ha n).1, (ha n).2⟩
  constructor
  · have origin : polynomialNomeSeries a 0 = 0 := by simp [polynomialNomeSeries]
    have nome : Tendsto (fun t : ℝ => Real.exp (-c * t)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, id_eq, neg_mul] using
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (Tendsto.const_mul_atTop hc (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
    have cont := (polynomialNomeSeries_hasDerivAt a bounds (q := 0)
      (by simp)).continuousAt.tendsto.comp nome
    simpa only [origin, Function.comp_def] using cont
  · apply tendsto_atTop.mpr
    intro B
    obtain ⟨N, hN⟩ := exists_nat_gt B
    let partialSum := fun t : ℝ => ∑ n ∈ Finset.range N, (Real.exp (-c * t)) ^ (n + 1)
    have ce : Continuous (fun t : ℝ => Real.exp (-c * t)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have cp : ContinuousAt partialSum 0 :=
      (continuous_finsetSum (Finset.range N) (fun n _ => ce.pow (n + 1))).continuousAt
    have cp0 : partialSum 0 = (N : ℝ) := by simp [partialSum]
    have win : ∀ᶠ t in 𝓝 (0 : ℝ), B < partialSum t :=
      cp.tendsto.eventually_const_lt (cp0.symm ▸ hN)
    filter_upwards [win.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht pos
    have tp : 0 < t := pos
    let q := Real.exp (-c * t)
    have qp : 0 < q := Real.exp_pos _
    have q1 : q < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) tp)
    have sm := polynomial_nome_summable a bounds qp.le q1
    calc
      B ≤ partialSum t := ht.le
      _ ≤ ∑ n ∈ Finset.range N, a n * q ^ (n + 1) := by
        apply Finset.sum_le_sum
        intro n _
        exact le_mul_of_one_le_left (pow_nonneg qp.le _) (ha n).1
      _ ≤ polynomialNomeSeries a q :=
        sm.sum_le_tsum _ (fun n _ => mul_nonneg (bounds n).1 (pow_nonneg qp.le _))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.polynomialNomeSeries_hasDerivAt
#print axioms TwoAxisHelicoid.polynomialNome_exponential_hasDerivAt
#print axioms TwoAxisHelicoid.polynomialNome_exponential_limits
