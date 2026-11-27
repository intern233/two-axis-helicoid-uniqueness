import TwoAxisHelicoid.VerticalRunBounds
import TwoAxisHelicoid.VerticalEndpoint
import Mathlib.Data.Rat.BigOperators

namespace TwoAxisHelicoid

namespace VerticalRun

private theorem cast_expCut (N : ℕ) (x : ℚ) :
    (expCut N x : ℝ) = expPolynomial N (x : ℝ) := by
  simp [expCut, expPolynomial, Rat.cast_sum]

private theorem cast_expError (N : ℕ) (x : ℚ) :
    (expError N x : ℝ) = |(x : ℝ)|^N / (N.factorial : ℝ) * 2 := by
  simp [expError]

private theorem expTest_sound (hp : (piLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpper : ℝ)) (N : ℕ) {t lo hi : ℚ} (ht : 0 < t) (ok : ExpTest N t lo hi) :
    (lo : ℝ) ≤ Real.exp (-Real.pi * (t : ℝ)) ∧
      Real.exp (-Real.pi * (t : ℝ)) ≤ (hi : ℝ) := by
  let a : ℚ := -piUpper*t
  let b : ℚ := -piLower*t
  obtain ⟨ha, hb, hlo, hhi⟩ := ok
  change |a| / ((N : ℚ)+1) ≤ 1/2 at ha
  change |b| / ((N : ℚ)+1) ≤ 1/2 at hb
  change lo ≤ expCut N a - expError N a at hlo
  change expCut N b + expError N b ≤ hi at hhi
  have ratio_real (x : ℚ) (h : |x| / ((N : ℚ)+1) ≤ 1/2) :
      |(x : ℝ)| / ((N : ℝ)+1) ≤ 1/2 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr h
  have ea := abs_le.mp (exp_polynomial_error (n := N) (x := (a : ℝ)) (ratio_real a ha))
  have eb := abs_le.mp (exp_polynomial_error (n := N) (x := (b : ℝ)) (ratio_real b hb))
  have l : (lo : ℝ) ≤ ((expCut N a-expError N a : ℚ) : ℝ) := by exact_mod_cast hlo
  have u : ((expCut N b+expError N b : ℚ) : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hhi
  rw [Rat.cast_sub, cast_expCut, cast_expError] at l
  rw [Rat.cast_add, cast_expCut, cast_expError] at u
  have tr : 0 ≤ (t : ℝ) := by exact_mod_cast ht.le
  have al : (a : ℝ) ≤ -Real.pi * (t : ℝ) := by
    simpa [a] using (mul_le_mul_of_nonneg_right (neg_le_neg hp.2) tr)
  have bu : -Real.pi * (t : ℝ) ≤ (b : ℝ) := by
    simpa [b] using (mul_le_mul_of_nonneg_right (neg_le_neg hp.1) tr)
  exact ⟨(show (lo : ℝ) ≤ Real.exp (a : ℝ) by linarith [ea.1]).trans (Real.exp_le_exp.mpr al),
    (Real.exp_le_exp.mpr bu).trans (by linarith [eb.2])⟩

/-- The real series enclosure follows from the stated π interval, the rational Taylor tests,
and the explicit positive-coefficient tail. -/
theorem displayed_series_bound_of_pi (hp : (piLower : ℝ) ≤ Real.pi ∧ Real.pi ≤ (piUpper : ℝ))
    {t lo hi L U : ℚ} (ht : 0 < t) (hl : 0 ≤ lo) (hh : hi < 1)
    (expOk : ExpTest 44 t lo hi) (seriesOk : SeriesTest 40 lo hi L U) :
    (L : ℝ) < verticalSeries (t : ℝ)/Real.pi^2 ∧ verticalSeries (t : ℝ)/Real.pi^2 < (U : ℝ) := by
  have tr : 0 < (t : ℝ) := by exact_mod_cast ht
  have he := expTest_sound hp 44 ht expOk
  apply normalized_vertical_mem_of_nome tr (by exact_mod_cast hl) (by exact_mod_cast hh) he.1 he.2 40
  · have h : (L : ℝ) < ((1/4 - 2*(seriesCut 40 hi + seriesTail 40 hi) : ℚ) : ℝ) := by
      exact_mod_cast seriesOk.1
    simpa [seriesCut, seriesTail, squareTail, Rat.cast_sum] using h
  · have h : ((1/4 - 2*seriesCut 40 lo : ℚ) : ℝ) < (U : ℝ) := by exact_mod_cast seriesOk.2
    simpa [seriesCut, Rat.cast_sum] using h

end VerticalRun
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.VerticalRun.displayed_series_bound_of_pi
