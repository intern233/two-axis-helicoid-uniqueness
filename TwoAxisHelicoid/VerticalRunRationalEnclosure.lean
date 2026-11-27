import TwoAxisHelicoid.VerticalRunSeriesEnclosure
import TwoAxisHelicoid.ManuscriptFEndpointEnclosures

namespace TwoAxisHelicoid.VerticalRun

/-- Every variable input is a rational number checked against Taylor's theorem,
the positive Fourier coefficients, and the explicit infinite tail. -/
theorem displayed_bound_of_tests {t lo hi L U : ℚ} (ht : 0 < t) (hl : 0 ≤ lo) (hh : hi < 1)
    (expOk : ExpTest 44 t lo hi) (seriesOk : SeriesTest 40 lo hi L U) :
    (L : ℝ) < ellipticFReal (t : ℝ)/Real.pi^2 ∧ ellipticFReal (t : ℝ)/Real.pi^2 < (U : ℝ) := by
  have tr : 0 < (t : ℝ) := by exact_mod_cast ht
  rw [ellipticFReal_eq_verticalSeries tr]
  exact displayed_series_bound_of_tests ht hl hh expOk seriesOk

end TwoAxisHelicoid.VerticalRun

#print axioms TwoAxisHelicoid.VerticalRun.displayed_bound_of_tests
