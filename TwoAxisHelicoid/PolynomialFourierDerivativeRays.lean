module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section
namespace TwoAxisHelicoid
open Filter Set
open scoped Topology

@[expose] noncomputable def polynomialFourierTerm (a : ℕ → ℝ) (c : ℝ) (k n : ℕ) (x : ℝ) : ℝ :=
  let f := -c * ((n + 1 : ℕ) : ℝ)
  a n * f ^ k * Real.exp (f * x)

private theorem polynomialFourierTerm_deriv (a : ℕ → ℝ) (c : ℝ) (k n : ℕ) (x : ℝ) :
    HasDerivAt (polynomialFourierTerm a c k n) (polynomialFourierTerm a c (k+1) n x) x := by
  let f := -c * ((n + 1 : ℕ) : ℝ)
  have e := ((hasDerivAt_id x).const_mul f).exp.const_mul (a n * f ^ k)
  change HasDerivAt (fun t => a n * f ^ k * Real.exp (f * t))
    (a n * f ^ (k + 1) * Real.exp (f * x)) x
  rw [show a n * f^(k+1) * Real.exp (f*x) =
      a n * f^k * (Real.exp (f*x) * (f*1)) by rw [pow_succ]; ring]
  exact e

/-- A single summable bound covers every parameter on the closed ray. -/
private theorem polynomialFourierTerm_majorant (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (k : ℕ) :
    ∃ M : ℕ → ℝ, Summable M ∧ ∀ n x, p ≤ x → ‖polynomialFourierTerm a c k n x‖ ≤ M n := by
  let q := Real.exp (-c * p)
  have qp : 0 < q := Real.exp_pos _
  have hq : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg qp.le]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hp)
  let g := fun j : ℕ => (j : ℝ) ^ (k+2) * q^j
  have sg : Summable g := summable_pow_mul_geometric_of_norm_lt_one (k+2) hq
  have shifted : Summable (fun n : ℕ => g (n+1)) := (summable_nat_add_iff (f := g) 1).mpr sg
  refine ⟨fun n => c^k * g (n+1), shifted.mul_left (c^k), ?_⟩
  intro n x hx
  let j : ℝ := ((n+1 : ℕ) : ℝ)
  have jp : 0 ≤ j := by dsimp [j]; positivity
  have rate : Real.exp ((-c*j)*x) ≤ q^(n+1) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (-c*j)*x ≤ (-c*j)*p :=
        mul_le_mul_of_nonpos_left hx (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) jp)
      _ = ((n+1 : ℕ) : ℝ) * (-c*p) := by dsimp only [j]; ring
  change |a n * (-c*j)^k * Real.exp ((-c*j)*x)| ≤ c^k * (j^(k+2)*q^(n+1))
  rw [abs_mul, abs_mul, abs_pow, abs_mul, abs_neg, abs_of_nonneg hc.le, abs_of_nonneg jp,
    abs_of_nonneg (ha n).1, abs_of_pos (Real.exp_pos _), mul_pow]
  calc
    _ ≤ (j^2 * (c^k * j^k)) * q^(n+1) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (ha n).2 (by positivity))
        rate (Real.exp_pos _).le (by positivity)
    _ = c^k * (j^(k+2)*q^(n+1)) := by rw [pow_add j k 2]; ring

/-- Ordinary partial sums of the differentiated series converge uniformly on
every closed ray with positive lower endpoint, for every derivative order. -/
theorem polynomialFourier_derivatives_uniform (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (k : ℕ) :
    TendstoUniformlyOn (fun N x => ∑ n ∈ Finset.range N, polynomialFourierTerm a c k n x)
      (fun x => ∑' n, polynomialFourierTerm a c k n x) atTop (Ici p) := by
  obtain ⟨M, sm, bound⟩ := polynomialFourierTerm_majorant a ha hc hp k
  exact tendstoUniformlyOn_tsum_nat sm bound

private theorem polynomialFourier_sum_deriv (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (k : ℕ) :
    HasDerivAt (fun y => ∑' n, polynomialFourierTerm a c k n y)
      (∑' n, polynomialFourierTerm a c (k+1) n x) x := by
  have hp : 0 < x/2 := by linarith
  have mem : x ∈ Ioi (x/2) := by change x/2 < x; linarith
  obtain ⟨M, sm, bd⟩ := polynomialFourierTerm_majorant a ha hc hp (k+1)
  obtain ⟨B, sb, origin⟩ := polynomialFourierTerm_majorant a ha hc hp k
  have sx : Summable (fun n => polynomialFourierTerm a c k n x) :=
    Summable.of_norm_bounded sb (fun n => origin n x (le_of_lt mem))
  exact hasDerivAt_tsum_of_isPreconnected (g := polynomialFourierTerm a c k)
    (g' := polynomialFourierTerm a c (k+1)) (t := Ioi (x/2)) (y₀ := x) (y := x)
    sm isOpen_Ioi isPreconnected_Ioi (fun n y _ => polynomialFourierTerm_deriv a c k n y)
    (fun n y hy => bd n y (le_of_lt hy)) mem sx mem

/-- The uniformly convergent expressions give the iterated real derivatives
of the sum on its whole positive parameter domain. -/
theorem polynomialFourier_sum_iteratedDeriv (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ ((n + 1 : ℕ) : ℝ) ^ 2)
    {c : ℝ} (hc : 0 < c) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (fun y => ∑' n, polynomialFourierTerm a c 0 n y) x =
      ∑' n, polynomialFourierTerm a c k n x := by
  induction k generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have germ : iteratedDeriv k (fun y => ∑' n, polynomialFourierTerm a c 0 n y)
        =ᶠ[𝓝 x] (fun y => ∑' n, polynomialFourierTerm a c k n y) :=
      (eventually_gt_nhds hx).mono (fun y hy => ih hy)
    exact germ.deriv_eq.trans (polynomialFourier_sum_deriv a ha hc hx k).deriv

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.polynomialFourier_derivatives_uniform
#print axioms TwoAxisHelicoid.polynomialFourier_sum_iteratedDeriv
