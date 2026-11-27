import TwoAxisHelicoid.OriginalPeriodBridge
import TwoAxisHelicoid.RootVerticalIncreasing
import TwoAxisHelicoid.RootCommonPeriodBridge
import TwoAxisHelicoid.RootDyadicLeftIntegral
import TwoAxisHelicoid.RootDyadicRightIntegral

namespace TwoAxisHelicoid
open Set
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
attribute [local irreducible] thetaG thetaHorizontalPeriod

/-- Equation two_axis_helicoid:eq-root-a-exact holds for every height of the full
closed localization interval. The original fractions are checked against
the endpoint vertical certificates using monotonicity on that interval. -/
theorem manuscript_exact_root_abscissa {t : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper) :
    verticalA t∈Icc (4409686737850678150959633307219/7427640235712281649394745344000 : ℝ)
      (4409686737857433550400689051219/7427640235712281649394745344000) := by
  let x : RootHeight := ⟨t,ht⟩
  have lo : rootLeftHeight≤x := ht.1
  have hi : x≤rootRightHeight := ht.2
  have lower : (rootVerticalA rootLeftHeight:ℝ)≤rootVerticalA x := rootVerticalA_strictMono.monotone lo
  have upper : (rootVerticalA x:ℝ)≤rootVerticalA rootRightHeight := rootVerticalA_strictMono.monotone hi
  rw [verticalA_eq_root_branch ht,rootVerticalAReal_eq ht]
  exact ⟨le_trans (by norm_num [rootLeftALower] : (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)≤rootLeftALower)
      (root_left_branch_localize.1.le.trans lower),
    upper.trans (root_right_branch_localize.2.le.trans (by norm_num [rootRightAUpper]))⟩

/-- Both strict enclosures of the original sloping period in equation
two_axis_helicoid:eq-root-signs. The rational comparisons are kernel reductions on
the same eighty validated quadrature cells and their error radii. -/
theorem manuscript_root_endpoint_period_enclosures :
    originalPeriodAlong rootTLower∈Ioo (63/10^13:ℝ) (64/10^13) ∧
    originalPeriodAlong rootTUpper∈Ioo (-37/10^13:ℝ) (-36/10^13) := by
  have left := dyadic_horizontal_half_bounds (by decide : 0<40) rootDyadicLeft rootDyadicLeft_valid rootDyadicLeftCells
    (1/20) (631/10^14) (633/10^14) rootDyadicLeftCells_valid (by decide +kernel) (by decide +kernel)
    (t:=rootTLower) le_rfl le_rfl le_rfl (by norm_num [rootTLower,rootTUpper])
    root_left_branch_localize.1.le root_left_branch_localize.2.le
  have right := dyadic_horizontal_half_bounds (by decide : 0<40) rootDyadicRight rootDyadicRight_valid rootDyadicRightCells
    (1/20) (-368/10^14) (-366/10^14) rootDyadicRightCells_valid (by decide +kernel) (by decide +kernel)
    (t:=rootTUpper) le_rfl le_rfl (by norm_num [rootTLower,rootTUpper]) le_rfl
    root_right_branch_localize.1.le root_right_branch_localize.2.le
  have identify (x : RootHeight) : originalPeriodAlong x=thetaHorizontalPeriod x (rootVerticalA x) := by
    rw [originalPeriodAlong_eq_actual (root_height_in_full_domain x.property)]
    change thetaHorizontalPeriod x (verticalA x)=_
    rw [verticalA_eq_root_branch x.property,rootVerticalAReal_eq x.property]
  rw [show originalPeriodAlong rootTLower=thetaHorizontalPeriod rootLeftHeight (rootVerticalA rootLeftHeight) from identify rootLeftHeight,
    show originalPeriodAlong rootTUpper=thetaHorizontalPeriod rootRightHeight (rootVerticalA rootRightHeight) from identify rootRightHeight]
  exact ⟨⟨lt_of_lt_of_le (by norm_num) left.1,lt_of_le_of_lt left.2 (by norm_num)⟩,
    ⟨lt_of_lt_of_le (by norm_num) right.1,lt_of_le_of_lt right.2 (by norm_num)⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.manuscript_exact_root_abscissa
#print axioms TwoAxisHelicoid.manuscript_root_endpoint_period_enclosures
