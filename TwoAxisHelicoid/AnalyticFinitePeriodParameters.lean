import TwoAxisHelicoid.LeftSignAll
import TwoAxisHelicoid.FullPeriodDiscrete

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology

theorem actualPeriodAlong_zero_height_gt_eighth {t : ℝ} (ht : 0 < t)
    (hz : actualPeriodAlong t = 0) : 1/8 < t := by
  by_contra! h
  exact (actualPeriodAlong_positive_left ht h).ne' hz

/-- The full scalar zero set is finite using the analytic left estimate,
the negative right-end limit and the identity theorem. No interval boxes
for the horizontal period or its derivative enter the argument. -/
theorem actualPeriodAlong_finite_zero_parameters_analytic :
    {t : ℝ | t ∈ Ioo 0 ellipticVerticalUpper ∧ actualPeriodAlong t = 0}.Finite := by
  apply (actualPeriodAlong_finite_zeros_above (show 0 < (1/8:ℝ) by norm_num)).subset
  intro t ht
  exact ⟨(actualPeriodAlong_zero_height_gt_eighth ht.1.1 ht.2).le,ht.1.2,ht.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actualPeriodAlong_finite_zero_parameters_analytic
