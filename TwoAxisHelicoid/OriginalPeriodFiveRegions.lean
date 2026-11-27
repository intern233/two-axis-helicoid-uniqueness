import TwoAxisHelicoid.PeriodHypothesesOnDomain
import TwoAxisHelicoid.GlobalPeriodUniqueness

namespace TwoAxisHelicoid
open Set

/-- All five lines of the table in the proof of Theorem 10.1 for the
manuscript's original sigma contour, using the independent chord bounds. -/
theorem original_sigma_period_five_regions : PeriodHypotheses originalPeriodAlong ellipticVerticalUpper :=
  actualPeriodHypotheses.transfer_on_domain (fun _ ht => originalPeriodAlong_eq_actual ht)

/-- The strict inequalities of Proposition 9.1 on the original sloping path.
This derivation uses the chord certificate and the contour identity. -/
theorem original_sigma_strict_bounds_from_chord :
    (∀ t ∈ Icc (1/8 : ℝ) (17/20), 3/10000 < originalPeriodAlong t) ∧
      ∀ t ∈ Icc (9/10 : ℝ) (7/5), originalPeriodAlong t < -(1/25 : ℝ) :=
  ⟨original_sigma_period_five_regions.positive, original_sigma_period_five_regions.negative⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_sigma_period_five_regions
#print axioms TwoAxisHelicoid.original_sigma_strict_bounds_from_chord
