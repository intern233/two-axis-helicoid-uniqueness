import TwoAxisHelicoid.VerticalRunCoreTests
import TwoAxisHelicoid.FourierCoefficients
import Mathlib.Data.Rat.BigOperators

namespace TwoAxisHelicoid.VerticalRun

private theorem core_prefix_eq (f : ℕ → ℚ) (n : ℕ) :
    VerticalRunCore.sumPrefix f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [VerticalRunCore.sumPrefix]
  | succ n ih => rw [VerticalRunCore.sumPrefix, ih, Finset.sum_range_succ]

private theorem core_factorial_eq (n : ℕ) : VerticalRunCore.factorial n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VerticalRunCore.factorial, Nat.factorial_succ, ih]

theorem core_abs_eq (x : ℚ) : x.abs = |x| := by
  change (if 0 ≤ x then x else -x) = |x|
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, abs_of_nonneg hx]
  · rw [ite_eq_right hx, abs_of_neg (lt_of_not_ge hx)]

theorem core_exp_cut_eq (x : ℚ) :
    VerticalRunCore.expCut x = ∑ k ∈ Finset.range 44, x^k / (k.factorial : ℚ) := by
  simp only [VerticalRunCore.expCut, core_prefix_eq, core_factorial_eq]

theorem core_exp_error_eq (x : ℚ) :
    VerticalRunCore.expError x = |x|^44 / ((44 : ℕ).factorial : ℚ) * 2 := by
  rw [VerticalRunCore.expError, core_factorial_eq, core_abs_eq]

set_option maxRecDepth 20000 in
private theorem core_coefficients_eq :
    ∀ i : Fin 40, VerticalRunCore.coefficient i.val = fourierCoefficientAt (i.val+1) := by
  decide +kernel

/-- The finite list in the core arithmetic check gives the genuine first
forty Fourier coefficients at positive indices. -/
theorem core_series_cut_eq (q : ℚ) :
    VerticalRunCore.seriesCut q =
      ∑ i ∈ Finset.range 40, (fourierCoefficientAt (i+1) : ℚ) * q^(i+1) := by
  rw [VerticalRunCore.seriesCut, core_prefix_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [core_coefficients_eq ⟨i, Finset.mem_range.mp hi⟩]

end TwoAxisHelicoid.VerticalRun

#print axioms TwoAxisHelicoid.VerticalRun.core_series_cut_eq
#print axioms TwoAxisHelicoid.VerticalRun.core_exp_cut_eq
