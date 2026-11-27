import TwoAxisHelicoid.ExpEnclosure
import TwoAxisHelicoid.VerticalSeries

/-!
# Vertical endpoint signs for the actual infinite series

This file proves the decimal endpoints in §5.3 for the series of (5.5),
including the link from finite rational arithmetic to the real exponential.
The separate identity between this series and eta + WeierstrassP is not
claimed here. No Python output is used as an assumption.
-/

namespace TwoAxisHelicoid
open Set

set_option maxRecDepth 10000
set_option maxHeartbeats 0

private theorem coefficient_1 : fourierCoefficientAt 1 = 1 := by decide +kernel
private theorem coefficient_2 : fourierCoefficientAt 2 = 1 := by decide +kernel
private theorem coefficient_3 : fourierCoefficientAt 3 = 4 := by decide +kernel
private theorem coefficient_4 : fourierCoefficientAt 4 = 5 := by decide +kernel
private theorem coefficient_5 : fourierCoefficientAt 5 = 6 := by decide +kernel
private theorem coefficient_6 : fourierCoefficientAt 6 = 4 := by decide +kernel
private theorem coefficient_7 : fourierCoefficientAt 7 = 8 := by decide +kernel
private theorem coefficient_8 : fourierCoefficientAt 8 = 13 := by decide +kernel
private theorem coefficient_9 : fourierCoefficientAt 9 = 13 := by decide +kernel
private theorem coefficient_10 : fourierCoefficientAt 10 = 6 := by decide +kernel
private theorem coefficient_11 : fourierCoefficientAt 11 = 12 := by decide +kernel
private theorem coefficient_12 : fourierCoefficientAt 12 = 20 := by decide +kernel
private theorem coefficient_13 : fourierCoefficientAt 13 = 14 := by decide +kernel
private theorem coefficient_14 : fourierCoefficientAt 14 = 8 := by decide +kernel
private theorem coefficient_15 : fourierCoefficientAt 15 = 24 := by decide +kernel
private theorem coefficient_16 : fourierCoefficientAt 16 = 29 := by decide +kernel

private theorem exp_left_lower :
    (10765392093268 / 100000000000000 : ℝ) ≤ Real.exp (-22288336328654310 / 10000000000000000) ∧
    Real.exp (-22288336328654310 / 10000000000000000) ≤ 10765392093269 / 100000000000000 := by
  apply exp_mem_of_polynomial (n := 26) (err := 1 / 10 ^ 17)
  all_goals norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

private theorem exp_left_upper :
    (10765392093268 / 100000000000000 : ℝ) ≤ Real.exp (-22288336328654309 / 10000000000000000) ∧
    Real.exp (-22288336328654309 / 10000000000000000) ≤ 10765392093269 / 100000000000000 := by
  apply exp_mem_of_polynomial (n := 26) (err := 1 / 10 ^ 17)
  all_goals norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

private theorem exp_right_lower :
    (10765391416858 / 100000000000000 : ℝ) ≤ Real.exp (-22288336956972840 / 10000000000000000) ∧
    Real.exp (-22288336956972840 / 10000000000000000) ≤ 10765391416859 / 100000000000000 := by
  apply exp_mem_of_polynomial (n := 26) (err := 1 / 10 ^ 17)
  all_goals norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

private theorem exp_right_upper :
    (10765391416858 / 100000000000000 : ℝ) ≤ Real.exp (-22288336956972839 / 10000000000000000) ∧
    Real.exp (-22288336956972839 / 10000000000000000) ≤ 10765391416859 / 100000000000000 := by
  apply exp_mem_of_polynomial (n := 26) (err := 1 / 10 ^ 17)
  all_goals norm_num [expPolynomial, Finset.sum_range_succ, Nat.factorial]

theorem nome_left_endpoint :
    (10765392093268 / 100000000000000 : ℝ) ≤ Real.exp (-Real.pi * (70945978 / 100000000)) ∧
    Real.exp (-Real.pi * (70945978 / 100000000)) ≤ 10765392093269 / 100000000000000 := by
  have harg : (-22288336328654310 / 10000000000000000 : ℝ) ≤
      -Real.pi * (70945978 / 100000000) ∧
      -Real.pi * (70945978 / 100000000) ≤ -22288336328654309 / 10000000000000000 := by
    constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]
  exact ⟨exp_left_lower.1.trans (Real.exp_le_exp.mpr harg.1),
    (Real.exp_le_exp.mpr harg.2).trans exp_left_upper.2⟩

theorem nome_right_endpoint :
    (10765391416858 / 100000000000000 : ℝ) ≤ Real.exp (-Real.pi * (70945980 / 100000000)) ∧
    Real.exp (-Real.pi * (70945980 / 100000000)) ≤ 10765391416859 / 100000000000000 := by
  have harg : (-22288336956972840 / 10000000000000000 : ℝ) ≤
      -Real.pi * (70945980 / 100000000) ∧
      -Real.pi * (70945980 / 100000000) ≤ -22288336956972839 / 10000000000000000 := by
    constructor <;> nlinarith [Real.pi_gt_d20, Real.pi_lt_d20]
  exact ⟨exp_right_lower.1.trans (Real.exp_le_exp.mpr harg.1),
    (Real.exp_le_exp.mpr harg.2).trans exp_right_upper.2⟩

/-- Enclose the actual infinite sum using a rational nome bracket. -/
theorem normalized_vertical_mem_of_nome {t qlo qhi L U : ℝ} (ht : 0 < t)
    (hlo : 0 ≤ qlo) (hhi : qhi < 1)
    (hql : qlo ≤ Real.exp (-Real.pi * t))
    (hqu : Real.exp (-Real.pi * t) ≤ qhi) (N : ℕ)
    (hL : L < 1 / 4 - 2 *
      ((∑ n ∈ Finset.range N, (fourierCoefficientAt (n+1) : ℝ) * qhi^(n+1)) +
        squareTail qhi N))
    (hU : 1 / 4 - 2 *
      (∑ n ∈ Finset.range N, (fourierCoefficientAt (n+1) : ℝ) * qlo^(n+1)) < U) :
    L < verticalSeries t / Real.pi^2 ∧ verticalSeries t / Real.pi^2 < U := by
  have hq := vertical_nome_mem ht
  have hqlo : qlo < 1 := hql.trans_lt hq.2
  have hqhi : 0 ≤ qhi := hq.1.le.trans hqu
  have hslo := qSeries_strictMonoOn.monotoneOn ⟨hlo, hqlo⟩ ⟨hq.1.le, hq.2⟩ hql
  have hshi := qSeries_strictMonoOn.monotoneOn ⟨hq.1.le, hq.2⟩ ⟨hqhi, hhi⟩ hqu
  have hloSum := (qSeries_partial_sum_bounds hlo hqlo N).1
  have hhiSum := (qSeries_partial_sum_bounds hqhi hhi N).2
  have hid : verticalSeries t / Real.pi^2 =
      1 / 4 - 2 * qSeries (Real.exp (-Real.pi*t)) := by
    rw [verticalSeries_eq_qSeries]
    field_simp
  rw [hid]
  constructor <;> linarith

theorem vertical_left_endpoint_normalized :
    (-48 / 10^10 : ℝ) < verticalSeries (70945978 / 100000000) / Real.pi^2 ∧
    verticalSeries (70945978 / 100000000) / Real.pi^2 < -47 / 10^10 := by
  apply normalized_vertical_mem_of_nome (qlo := 10765392093268 / 100000000000000)
    (qhi := 10765392093269 / 100000000000000) (by norm_num) (by norm_num) (by norm_num)
    nome_left_endpoint.1 nome_left_endpoint.2 16
  all_goals norm_num [Finset.sum_range_succ, squareTail, coefficient_1, coefficient_2, coefficient_3, coefficient_4, coefficient_5, coefficient_6, coefficient_7, coefficient_8, coefficient_9, coefficient_10, coefficient_11, coefficient_12, coefficient_13, coefficient_14, coefficient_15, coefficient_16]

theorem vertical_right_endpoint_normalized :
    (139 / 10^10 : ℝ) < verticalSeries (70945980 / 100000000) / Real.pi^2 ∧
    verticalSeries (70945980 / 100000000) / Real.pi^2 < 140 / 10^10 := by
  apply normalized_vertical_mem_of_nome (qlo := 10765391416858 / 100000000000000)
    (qhi := 10765391416859 / 100000000000000) (by norm_num) (by norm_num) (by norm_num)
    nome_right_endpoint.1 nome_right_endpoint.2 16
  all_goals norm_num [Finset.sum_range_succ, squareTail, coefficient_1, coefficient_2, coefficient_3, coefficient_4, coefficient_5, coefficient_6, coefficient_7, coefficient_8, coefficient_9, coefficient_10, coefficient_11, coefficient_12, coefficient_13, coefficient_14, coefficient_15, coefficient_16]

theorem vertical_left_endpoint_neg : verticalSeries (70945978 / 100000000) < 0 := by
  have h := vertical_left_endpoint_normalized.2
  have hp : (0 : ℝ) < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hn : verticalSeries (70945978 / 100000000) / Real.pi^2 < 0 := by linarith
  simpa using (div_lt_iff₀ hp).mp hn

theorem vertical_right_endpoint_pos : 0 < verticalSeries (70945980 / 100000000) := by
  have h := vertical_right_endpoint_normalized.1
  have hp : (0 : ℝ) < Real.pi^2 := sq_pos_of_pos Real.pi_pos
  have hn : 0 < verticalSeries (70945980 / 100000000) / Real.pi^2 := by linarith
  exact (div_pos_iff_of_pos_right hp).mp hn

/-- The exact decimal interval for the unique positive root of the series. -/
theorem vertical_root_exact_location {t : ℝ} (ht : 0 < t) (hz : verticalSeries t = 0) :
    (70945978 / 100000000 : ℝ) < t ∧ t < 70945980 / 100000000 := by
  constructor
  · by_contra hn
    have hm := verticalSeries_strictMonoOn.monotoneOn ht
      (by norm_num : (0 : ℝ) < 70945978 / 100000000) (le_of_not_gt hn)
    linarith [vertical_left_endpoint_neg]
  · by_contra hn
    have hm := verticalSeries_strictMonoOn.monotoneOn
      (by norm_num : (0 : ℝ) < 70945980 / 100000000) ht (le_of_not_gt hn)
    linarith [vertical_right_endpoint_pos]

theorem existsUnique_verticalSeries_root_located :
    ∃! t : ℝ, (70945978 / 100000000 : ℝ) < t ∧
      t < 70945980 / 100000000 ∧ verticalSeries t = 0 := by
  obtain ⟨t, ⟨ht, hz⟩, hu⟩ := existsUnique_verticalSeries_root
  have hl := vertical_root_exact_location ht hz
  refine ⟨t, ⟨hl.1, hl.2, hz⟩, ?_⟩
  intro y hy
  exact hu y ⟨by linarith [hy.1], hy.2.2⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.nome_left_endpoint
#print axioms TwoAxisHelicoid.vertical_left_endpoint_normalized
#print axioms TwoAxisHelicoid.vertical_right_endpoint_normalized
#print axioms TwoAxisHelicoid.existsUnique_verticalSeries_root_located

