import TwoAxisHelicoid.FourierCoefficients
import TwoAxisHelicoid.SeriesTail
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# The actual positive-coefficient series in (5.5)

The index `n + 1` enumerates all positive indices. These definitions use
the divisor-sum coefficients proved in `FourierCoefficients`. Convergence,
monotonicity, continuity, and the explicit tail bound are mathematical
theorems about these infinite sums. The identity with `η(t) + ℘ₜ(1)` is a
separate, still unformalized elliptic-function obligation.
-/

open Set
open scoped Topology

namespace TwoAxisHelicoid

noncomputable def qSeries (q : ℝ) : ℝ :=
  ∑' n : ℕ, (fourierCoefficientAt (n + 1) : ℝ) * q ^ (n + 1)

noncomputable def verticalSeries (t : ℝ) : ℝ :=
  Real.pi ^ 2 * (1 / 4 - 2 *
    ∑' n : ℕ, (fourierCoefficientAt (n + 1) : ℝ) *
      Real.exp (-Real.pi * (n + 1) * t))

private theorem coefficient_nonneg (n : ℕ) :
    0 ≤ (fourierCoefficientAt n : ℝ) := Nat.cast_nonneg _

private theorem coefficient_upper (n : ℕ) :
    (fourierCoefficientAt n : ℝ) ≤ (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [fourierCoefficientAt, fourierCoefficient]
  · exact_mod_cast (fourier_coefficient_at_bounds hn).2

private theorem coefficient_lower (n : ℕ) :
    (1 : ℝ) ≤ fourierCoefficientAt (n + 1) := by
  exact_mod_cast (fourier_coefficient_at_bounds (Nat.succ_pos n)).1

/-- Convergence on the full nome range, including the limiting value `q = 0`. -/
theorem summable_qSeries {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => (fourierCoefficientAt (n + 1) : ℝ) * q ^ (n + 1)) := by
  have hmajor : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * q ^ (n + 1)) := by
    simpa using (hasSum_square_tail hq0 hq1 0).summable
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (coefficient_nonneg _) (pow_nonneg hq0 _))
    (fun n => mul_le_mul_of_nonneg_right (coefficient_upper _) (pow_nonneg hq0 _)) hmajor

/-- Increasing the nome strictly increases the infinite sum. -/
theorem qSeries_strictMonoOn : StrictMonoOn qSeries (Ico 0 1) := by
  intro x hx y hy hxy
  have hterms : ∀ n : ℕ,
      (fourierCoefficientAt (n + 1) : ℝ) * x ^ (n + 1) ≤
      (fourierCoefficientAt (n + 1) : ℝ) * y ^ (n + 1) :=
    fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hxy.le _) (coefficient_nonneg _)
  have hfirst : (fourierCoefficientAt (0 + 1) : ℝ) * x ^ (0 + 1) <
      (fourierCoefficientAt (0 + 1) : ℝ) * y ^ (0 + 1) := by
    simp only [zero_add, pow_one]
    exact mul_lt_mul_of_pos_left hxy (lt_of_lt_of_le zero_lt_one (coefficient_lower 0))
  exact Summable.tsum_lt_tsum hterms hfirst
    (summable_qSeries hx.1 hx.2) (summable_qSeries hy.1 hy.2)

/-- The explicit tail bound now applies to the actual coefficients. -/
theorem qSeries_tail_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑' n : ℕ, (fourierCoefficientAt (n + N + 1) : ℝ) * q ^ (n + N + 1))
      ≤ squareTail q N :=
  coefficient_tail_bound hq0 hq1 (fun n => (fourierCoefficientAt n : ℝ))
    coefficient_nonneg coefficient_upper N

/-- The usual finite partial-sum enclosure is proved from convergence,
not postulated as a numerical oracle. -/
theorem qSeries_partial_sum_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑ n ∈ Finset.range N, (fourierCoefficientAt (n + 1) : ℝ) * q ^ (n + 1)) ≤ qSeries q ∧
    qSeries q ≤
      (∑ n ∈ Finset.range N, (fourierCoefficientAt (n + 1) : ℝ) * q ^ (n + 1)) +
      squareTail q N := by
  have hsplit := (summable_qSeries hq0 hq1).sum_add_tsum_nat_add N
  change _ = qSeries q at hsplit
  have htail0 : 0 ≤ ∑' n : ℕ,
      (fourierCoefficientAt (n + N + 1) : ℝ) * q ^ (n + N + 1) :=
    tsum_nonneg (fun n => mul_nonneg (coefficient_nonneg _) (pow_nonneg hq0 _))
  have htail := qSeries_tail_bound hq0 hq1 N
  constructor <;> linarith

/-- Continuity follows from the square-geometric uniform majorant. -/
theorem continuousOn_qSeries_Icc {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ContinuousOn qSeries (Icc 0 r) := by
  apply continuousOn_tsum
      (u := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * r ^ (n + 1))
  · intro n
    exact (continuous_const.mul (continuous_id.pow _)).continuousOn
  · simpa using (hasSum_square_tail hr0 hr1 0).summable
  · intro n x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (coefficient_nonneg _) (pow_nonneg hx.1 _))]
    exact mul_le_mul (coefficient_upper _)
      (pow_le_pow_left₀ hx.1 hx.2 _) (pow_nonneg hx.1 _) (sq_nonneg _)

theorem continuousAt_qSeries {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ContinuousAt qSeries q := by
  obtain ⟨r, hqr, hr1⟩ := exists_between hq1
  exact (continuousOn_qSeries_Icc (hq0.le.trans hqr.le) hr1).continuousAt
    (Icc_mem_nhds hq0 hqr)

/-- Rewriting the exponential series in terms of its nome is exact. -/
theorem verticalSeries_eq_qSeries (t : ℝ) :
    verticalSeries t = Real.pi ^ 2 * (1 / 4 - 2 * qSeries (Real.exp (-Real.pi * t))) := by
  unfold verticalSeries qSeries
  congr 3
  apply tsum_congr
  intro n
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem vertical_nome_mem {t : ℝ} (ht : 0 < t) :
    Real.exp (-Real.pi * t) ∈ Ioo 0 1 := by
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ht)⟩

theorem summable_verticalSeries {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => (fourierCoefficientAt (n + 1) : ℝ) *
      Real.exp (-Real.pi * (n + 1) * t)) := by
  have hq := vertical_nome_mem ht
  have hs := summable_qSeries hq.1.le hq.2
  apply hs.congr
  intro n
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The series-defined vertical function is strictly increasing on `t > 0`. -/
theorem verticalSeries_strictMonoOn : StrictMonoOn verticalSeries (Ioi 0) := by
  intro x hx y hy hxy
  have hqx := vertical_nome_mem hx
  have hqy := vertical_nome_mem hy
  have hqxy : Real.exp (-Real.pi * y) < Real.exp (-Real.pi * x) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [Real.pi_pos]
  have hs := qSeries_strictMonoOn ⟨hqy.1.le, hqy.2⟩ ⟨hqx.1.le, hqx.2⟩ hqxy
  rw [verticalSeries_eq_qSeries, verticalSeries_eq_qSeries]
  apply mul_lt_mul_of_pos_left _ (sq_pos_of_pos Real.pi_pos)
  linarith

theorem continuousOn_verticalSeries : ContinuousOn verticalSeries (Ioi 0) := by
  intro t ht
  have hn : ContinuousAt (fun x : ℝ => Real.exp (-Real.pi * x)) t := by fun_prop
  have hq := vertical_nome_mem ht
  have hc := (continuousAt_qSeries hq.1 hq.2).comp
    (f := fun x : ℝ => Real.exp (-Real.pi * x)) hn
  have hv : ContinuousAt
      (fun x : ℝ => Real.pi ^ 2 * (1 / 4 - 2 * qSeries (Real.exp (-Real.pi * x)))) t :=
    continuousAt_const.mul (continuousAt_const.sub (continuousAt_const.mul hc))
  simpa only [← verticalSeries_eq_qSeries] using hv.continuousWithinAt

/-- A coarse rational left endpoint for the nome equation. This is proved
using the genuine infinite-series tail bound, without interval-program output. -/
theorem qSeries_one_sixteenth_lt : qSeries (1 / 16) < 1 / 8 := by
  calc
    qSeries (1 / 16) ≤ squareTail (1 / 16) 0 := by
      simpa [qSeries] using qSeries_tail_bound (q := 1 / 16) (by norm_num) (by norm_num) 0
    _ < 1 / 8 := by norm_num [squareTail]

/-- A coarse rational right endpoint for the nome equation, using the first term. -/
theorem one_eighth_lt_qSeries_one_quarter : 1 / 8 < qSeries (1 / 4) := by
  have hs := summable_qSeries (q := 1 / 4) (by norm_num) (by norm_num)
  have hfirst := hs.le_tsum 0 (fun n _ =>
    mul_nonneg (coefficient_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) _))
  have hcoef := coefficient_lower 0
  simp only [zero_add, pow_one] at hfirst hcoef
  change _ ≤ qSeries (1 / 4) at hfirst
  nlinarith

/-- Existence and global uniqueness of the solution of `S(q) = 1/8`.
The rational bracket is deliberately coarse and independent of the PDF's
external numerical certificate. -/
theorem existsUnique_qSeries_root :
    ∃! q : ℝ, q ∈ Ioo 0 1 ∧ qSeries q = 1 / 8 := by
  have hc : ContinuousOn qSeries (Icc (1 / 16) (1 / 4)) :=
    (continuousOn_qSeries_Icc (r := 1 / 4) (by norm_num) (by norm_num)).mono
      (Icc_subset_Icc (by norm_num) le_rfl)
  obtain ⟨q, hq, heq⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) / 16 ≤ 1 / 4) hc
    ⟨qSeries_one_sixteenth_lt.le, one_eighth_lt_qSeries_one_quarter.le⟩
  have hq01 : q ∈ Ioo 0 1 := by constructor <;> linarith [hq.1, hq.2]
  refine ⟨q, ⟨hq01, heq⟩, ?_⟩
  intro y hy
  apply qSeries_strictMonoOn.injOn ⟨hy.1.1.le, hy.1.2⟩ ⟨hq01.1.le, hq01.2⟩
  exact hy.2.trans heq.symm

/-- The series-defined `F(t)` has exactly one positive root.
This still does not identify `F` with the geometric vertical-period function. -/
theorem existsUnique_verticalSeries_root :
    ∃! t : ℝ, 0 < t ∧ verticalSeries t = 0 := by
  obtain ⟨q, ⟨hq, hSq⟩, _⟩ := existsUnique_qSeries_root
  let t := -Real.log q / Real.pi
  have ht : 0 < t := div_pos (neg_pos.mpr (Real.log_neg hq.1 hq.2)) Real.pi_pos
  have hnome : Real.exp (-Real.pi * t) = q := by
    have harg : -Real.pi * t = Real.log q := by
      dsimp [t]
      field_simp
    rw [harg, Real.exp_log hq.1]
  have hzero : verticalSeries t = 0 := by
    rw [verticalSeries_eq_qSeries, hnome, hSq]
    ring
  refine ⟨t, ⟨ht, hzero⟩, ?_⟩
  intro s hs
  exact verticalSeries_strictMonoOn.injOn hs.1 ht (hs.2.trans hzero.symm)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.summable_qSeries
#print axioms TwoAxisHelicoid.qSeries_strictMonoOn
#print axioms TwoAxisHelicoid.qSeries_partial_sum_bounds
#print axioms TwoAxisHelicoid.verticalSeries_strictMonoOn
#print axioms TwoAxisHelicoid.continuousOn_verticalSeries
#print axioms TwoAxisHelicoid.existsUnique_qSeries_root
#print axioms TwoAxisHelicoid.existsUnique_verticalSeries_root
