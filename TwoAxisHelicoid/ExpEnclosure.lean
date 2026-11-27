import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Finite polynomial enclosures linked to the actual real exponential. -/

namespace TwoAxisHelicoid

noncomputable def expPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)

/-- A Taylor error bound for arbitrary real arguments, not just `|x| ≤ 1`. -/
theorem exp_polynomial_error {x : ℝ} {n : ℕ}
    (h : |x| / (n + 1) ≤ 1 / 2) :
    |Real.exp x - expPolynomial n x| ≤ |x| ^ n / (n.factorial : ℝ) * 2 := by
  have hc : ‖(x : ℂ)‖ / (n + 1) ≤ 1 / 2 := by simpa using h
  have hb := Complex.exp_bound' (x := (x : ℂ)) (n := n)
    (by simpa only [Nat.cast_succ] using hc)
  simpa only [expPolynomial, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div, ← Complex.ofReal_sum, ← Complex.ofReal_exp,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hb

/-- Every condition here is a finite real/rational inequality, except for the
actual exponential in the conclusion. The Taylor theorem discharges that gap. -/
theorem exp_mem_of_polynomial {x lo hi err : ℝ} {n : ℕ}
    (hx : |x| / (n + 1) ≤ 1 / 2)
    (herr : |x| ^ n / (n.factorial : ℝ) * 2 ≤ err)
    (hl : lo ≤ expPolynomial n x - err)
    (hu : expPolynomial n x + err ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have hb := abs_le.mp (exp_polynomial_error hx)
  constructor <;> linarith [hb.1, hb.2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exp_polynomial_error
#print axioms TwoAxisHelicoid.exp_mem_of_polynomial
