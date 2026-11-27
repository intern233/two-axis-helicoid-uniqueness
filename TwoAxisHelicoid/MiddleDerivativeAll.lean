import TwoAxisHelicoid.UnitIntervalCover
import TwoAxisHelicoid.MiddlePeriodConsequences
import TwoAxisHelicoid.MiddleDerivativeBox000
import TwoAxisHelicoid.MiddleDerivativeBox001
import TwoAxisHelicoid.MiddleDerivativeBox002
import TwoAxisHelicoid.MiddleDerivativeBox003
import TwoAxisHelicoid.MiddleDerivativeBox004
import TwoAxisHelicoid.MiddleDerivativeBox005
import TwoAxisHelicoid.MiddleDerivativeBox006
import TwoAxisHelicoid.MiddleDerivativeBox007
import TwoAxisHelicoid.MiddleDerivativeBox008
import TwoAxisHelicoid.MiddleDerivativeBox009
import TwoAxisHelicoid.MiddleDerivativeBox010
import TwoAxisHelicoid.MiddleDerivativeBox011
import TwoAxisHelicoid.MiddleDerivativeBox012
import TwoAxisHelicoid.MiddleDerivativeBox013
import TwoAxisHelicoid.MiddleDerivativeBox014
import TwoAxisHelicoid.MiddleDerivativeBox015
import TwoAxisHelicoid.MiddleDerivativeBox016
import TwoAxisHelicoid.MiddleDerivativeBox017
import TwoAxisHelicoid.MiddleDerivativeBox018
import TwoAxisHelicoid.MiddleDerivativeBox019
import TwoAxisHelicoid.MiddleDerivativeBox020
import TwoAxisHelicoid.MiddleDerivativeBox021
import TwoAxisHelicoid.MiddleDerivativeBox022
import TwoAxisHelicoid.MiddleDerivativeBox023
import TwoAxisHelicoid.MiddleDerivativeBox024
import TwoAxisHelicoid.MiddleDerivativeBox025
import TwoAxisHelicoid.MiddleDerivativeBox026
import TwoAxisHelicoid.MiddleDerivativeBox027
import TwoAxisHelicoid.MiddleDerivativeBox028
import TwoAxisHelicoid.MiddleDerivativeBox029
import TwoAxisHelicoid.MiddleDerivativeBox030
import TwoAxisHelicoid.MiddleDerivativeBox031
import TwoAxisHelicoid.MiddleDerivativeBox032
import TwoAxisHelicoid.MiddleDerivativeBox033
import TwoAxisHelicoid.MiddleDerivativeBox034
import TwoAxisHelicoid.MiddleDerivativeBox035
import TwoAxisHelicoid.MiddleDerivativeBox036
import TwoAxisHelicoid.MiddleDerivativeBox037
import TwoAxisHelicoid.MiddleDerivativeBox038
import TwoAxisHelicoid.MiddleDerivativeBox039
import TwoAxisHelicoid.MiddleDerivativeBox040
import TwoAxisHelicoid.MiddleDerivativeBox041
import TwoAxisHelicoid.MiddleDerivativeBox042
import TwoAxisHelicoid.MiddleDerivativeBox043
import TwoAxisHelicoid.MiddleDerivativeBox044
import TwoAxisHelicoid.MiddleDerivativeBox045
import TwoAxisHelicoid.MiddleDerivativeBox046
import TwoAxisHelicoid.MiddleDerivativeBox047
import TwoAxisHelicoid.MiddleDerivativeBox048
import TwoAxisHelicoid.MiddleDerivativeBox049
namespace TwoAxisHelicoid
open ComplexBall
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem actualPeriodAlong_deriv_lt_neg_one_middle {t : ℝ} (htl : (17/20 : ℝ) ≤ t) (htu : t ≤ (9/10 : ℝ)) : deriv actualPeriodAlong t < -1 := by
  obtain ⟨i,hil,hiu⟩ := middle_parameter_partition htl htu
  fin_cases i
  · apply middleDerivativeBox000_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox001_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox002_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox003_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox004_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox005_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox006_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox007_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox008_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox009_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox010_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox011_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox012_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox013_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox014_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox015_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox016_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox017_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox018_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox019_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox020_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox021_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox022_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox023_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox024_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox025_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox026_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox027_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox028_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox029_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox030_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox031_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox032_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox033_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox034_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox035_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox036_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox037_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox038_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox039_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox040_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox041_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox042_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox043_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox044_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox045_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox046_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox047_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox048_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
  · apply middleDerivativeBox049_derivative
    · norm_num at hil ⊢; linarith
    · norm_num at hiu ⊢; linarith
theorem actualPeriodAlong_strictAntiOn_middle :
    StrictAntiOn actualPeriodAlong (Set.Icc (17/20 : ℝ) (9/10)) := by
  apply actualPeriodAlong_strictAntiOn_middle_of_deriv_neg
  intro t ht
  exact (actualPeriodAlong_deriv_lt_neg_one_middle ht.1 ht.2).trans (by norm_num)

/-- The full closed middle interval has exactly one zero of the actual
horizontal period along the actual vertical branch. This is a middle-
interval conclusion, not uniqueness on the whole solvability domain. -/
theorem existsUnique_actualPeriodAlong_root_middle :
    ∃! t : ℝ, t ∈ Set.Icc (17/20 : ℝ) (9/10) ∧ actualPeriodAlong t = 0 :=
  existsUnique_actualPeriodAlong_root_middle_of_strictAnti actualPeriodAlong_strictAntiOn_middle

theorem existsUnique_actual_common_period_middle :
    ∃! p : ℝ × ℝ, p.1 ∈ Set.Icc (17/20 : ℝ) (9/10) ∧
      p.2 ∈ Set.Ioo (0 : ℝ) 1 ∧ thetaG p.1 p.2 = 0 ∧ thetaHorizontalPeriod p.1 p.2 = 0 :=
  existsUnique_common_period_middle_of_strictAnti actualPeriodAlong_strictAntiOn_middle

theorem actualPeriodAlong_middle_root_certified_location {t : ℝ}
    (ht : t ∈ Set.Icc (17/20 : ℝ) (9/10)) (hz : actualPeriodAlong t = 0) :
    t ∈ Set.Ioo (rootTLower : ℝ) rootTUpper ∧
      verticalA t ∈ Set.Ioo (rootALower : ℝ) rootAUpper ∧ deriv actualPeriodAlong t < -8 :=
  actualPeriodAlong_middle_root_location_of_strictAnti actualPeriodAlong_strictAntiOn_middle ht hz

theorem actualPeriodAlong_middle_endpoint_signs :
    0 < actualPeriodAlong (17/20) ∧ actualPeriodAlong (9/10) < 0 :=
  actualPeriodAlong_middle_endpoint_signs_of_strictAnti actualPeriodAlong_strictAntiOn_middle

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.existsUnique_actual_common_period_middle
#print axioms TwoAxisHelicoid.actualPeriodAlong_deriv_lt_neg_one_middle
