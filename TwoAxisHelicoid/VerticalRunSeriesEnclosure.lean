import TwoAxisHelicoid.VerticalRunSeriesFromPi
import TwoAxisHelicoid.VerticalFineMachinPi

namespace TwoAxisHelicoid.VerticalRun

/-- The normalized Fourier sum is enclosed using the fine π interval from the
two arctangent sums of the original attachment, the exponential Taylor tests
and the explicit infinite-series tail. -/
theorem displayed_series_bound_of_tests {t lo hi L U : ℚ} (ht : 0 < t) (hl : 0 ≤ lo) (hh : hi < 1)
    (expOk : ExpTest 44 t lo hi) (seriesOk : SeriesTest 40 lo hi L U) :
    (L : ℝ) < verticalSeries (t : ℝ)/Real.pi^2 ∧ verticalSeries (t : ℝ)/Real.pi^2 < (U : ℝ) :=
  displayed_series_bound_of_pi VerticalAttachment.uploaded_machin_fine_pi ht hl hh expOk seriesOk

end TwoAxisHelicoid.VerticalRun

#print axioms TwoAxisHelicoid.VerticalRun.displayed_series_bound_of_tests
