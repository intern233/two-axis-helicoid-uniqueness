import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# The genuine infinite-series tail calculation in (5.8)

The index `n + N + 1`, with `n : ℕ`, enumerates precisely the indices greater
than `N`.  The identification and bounds of the PDF's Fourier coefficients
are separate obligations; no elliptic-function identity is assumed here.
-/

namespace TwoAxisHelicoid

noncomputable def squareTail (q : ℝ) (N : ℕ) : ℝ :=
  q ^ (N + 1) * (((N : ℝ) + 1) ^ 2 / (1 - q) +
    2 * ((N : ℝ) + 1) * q / (1 - q) ^ 2 + q * (1 + q) / (1 - q) ^ 3)

theorem hasSum_square_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    HasSum (fun n : ℕ => ((n + N + 1 : ℕ) : ℝ) ^ 2 * q ^ (n + N + 1))
      (squareTail q N) := by
  have hq : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have h0 := (hasSum_geometric_of_norm_lt_one hq).mul_left (((N : ℝ) + 1) ^ 2)
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hq).mul_left (2 * ((N : ℝ) + 1))
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one hq
  convert ((h0.add h1).add h2).mul_left (q ^ (N + 1)) using 1
  · ext n
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show n + N + 1 = n + (N + 1) by omega, pow_add]
    ring
  · unfold squareTail
    ring

/-- Formula (5.8), including convergence of the infinite majorant. -/
theorem tsum_square_tail {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ 2 * q ^ (n + N + 1)) = squareTail q N :=
  (hasSum_square_tail hq0 hq1 N).tsum_eq

/-- Apply the tail bound to any nonnegative coefficients bounded by `n²`. -/
theorem coefficient_tail_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n) (hb2 : ∀ n, b n ≤ (n : ℝ) ^ 2) (N : ℕ) :
    (∑' n : ℕ, b (n + N + 1) * q ^ (n + N + 1)) ≤ squareTail q N := by
  have hmajor := (hasSum_square_tail hq0 hq1 N).summable
  have hnonneg : ∀ n : ℕ, 0 ≤ b (n + N + 1) * q ^ (n + N + 1) :=
    fun n => mul_nonneg (hb0 _) (pow_nonneg hq0 _)
  have hle : ∀ n : ℕ, b (n + N + 1) * q ^ (n + N + 1) ≤
      ((n + N + 1 : ℕ) : ℝ) ^ 2 * q ^ (n + N + 1) :=
    fun n => mul_le_mul_of_nonneg_right (hb2 _) (pow_nonneg hq0 _)
  have hminor := Summable.of_nonneg_of_le hnonneg hle hmajor
  rw [← tsum_square_tail hq0 hq1 N]
  exact hminor.tsum_le_tsum hle hmajor

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.hasSum_square_tail
#print axioms TwoAxisHelicoid.coefficient_tail_bound
