import TwoAxisHelicoid.RightVerticalBoundaryData
import TwoAxisHelicoid.RangePeriodBounds
namespace TwoAxisHelicoid
theorem right_vertical_boundary_gt_one_twentieth {t : ℝ}
    (htl : (7/5 : ℝ) ≤ t) (htu : t ≤ (141/100 : ℝ)) :
    (1/20 : ℝ) < (thetaG t (9/10)).re := by
  have hp := rightVerticalBoundaryParameters.sound middleRangeSetup middleRangeSetup_valid
    rightVerticalBoundaryParameters_valid (t := t) (a := (9/10 : ℝ))
    (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htl)
    (by simpa only [Rat.cast_div, Rat.cast_ofNat] using htu) (by norm_num) (by norm_num)
  have hg := rightVerticalBoundaryParameters.vertical_sound middleRangeSetup hp
    rightVerticalBoundaryTrace rightVerticalBoundaryTrace_valid
  have hl : (((1/20 : ℚ) : ℝ)) <
      (((rightVerticalBoundaryTrace.output.toBall middleRangeSetup.config.prec).center.re -
        (rightVerticalBoundaryTrace.output.toBall middleRangeSetup.config.prec).radius : ℚ) : ℝ) :=
    Rat.cast_lt.mpr rightVerticalBoundaryTrace_lower
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hl
  exact hl.trans_le (ComplexBall.re_bounds hg).1

theorem actual_right_parameters_in_rectangle {t : ℝ}
    (htl : (7/5 : ℝ) ≤ t) (htu : t < ellipticVerticalUpper) :
    t ∈ Set.Icc (7/5 : ℝ) (141/100) ∧ verticalA t ∈ Set.Ioo (9/10 : ℝ) 1 := by
  have ht : t ∈ Set.Ioo (0 : ℝ) ellipticVerticalUpper :=
    ⟨lt_of_lt_of_le (by norm_num) htl, htu⟩
  have htop : t < (141/100 : ℝ) := htu.trans
    (ellipticVerticalUpper_location.2.trans (by norm_num))
  have ha := verticalA_spec ht
  refine ⟨⟨htl, htop.le⟩, ?_, ha.1.2⟩
  have hg := right_vertical_boundary_gt_one_twentieth htl htop.le
  by_contra hn
  have hm := (thetaG_strictAnti_unit_of_pos ht.1).antitoneOn ha.1
    (by norm_num : (9/10 : ℝ) ∈ Set.Ioo (0 : ℝ) 1) (le_of_not_gt hn)
  change (thetaG t (9/10)).re ≤ (thetaG t (verticalA t)).re at hm
  rw [ha.2] at hm
  norm_num at hm
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.right_vertical_boundary_gt_one_twentieth
#print axioms TwoAxisHelicoid.actual_right_parameters_in_rectangle
