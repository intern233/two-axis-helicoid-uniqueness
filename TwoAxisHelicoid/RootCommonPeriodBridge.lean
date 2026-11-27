import TwoAxisHelicoid.RootPeriodContinuity
import TwoAxisHelicoid.RootEndpointVertical

namespace TwoAxisHelicoid
open Set
attribute [local irreducible] thetaG thetaJet thetaTerm thetaQuotient thetaA thetaHorizontalPeriod

noncomputable def rootLeftHeight : RootHeight :=
  ⟨rootTLower, le_rfl, by norm_num [rootTLower, rootTUpper]⟩

noncomputable def rootRightHeight : RootHeight :=
  ⟨rootTUpper, by norm_num [rootTLower, rootTUpper], le_rfl⟩

theorem root_left_branch_localize :
    (rootVerticalA rootLeftHeight : ℝ) ∈ Ioo (rootLeftALower : ℝ) rootLeftAUpper :=
  root_left_vertical_localize (rootVerticalA rootLeftHeight).property (rootVerticalA_spec rootLeftHeight).2

theorem root_right_branch_localize :
    (rootVerticalA rootRightHeight : ℝ) ∈ Ioo (rootRightALower : ℝ) rootRightAUpper :=
  root_right_vertical_localize (rootVerticalA rootRightHeight).property (rootVerticalA_spec rootRightHeight).2

/-- The continuity and the vertical equation are proved here; only the two
endpoint signs are inputs to this intermediate-value assembly lemma. -/
theorem exists_common_period_zero_of_endpoint_signs
    (hl : 0 < thetaHorizontalPeriod rootLeftHeight (rootVerticalA rootLeftHeight))
    (hr : thetaHorizontalPeriod rootRightHeight (rootVerticalA rootRightHeight) < 0) :
    ∃ t a : ℝ, t ∈ Ioo (rootTLower : ℝ) rootTUpper ∧
      a ∈ Ioo (rootALower : ℝ) rootAUpper ∧ thetaG t a = 0 ∧ thetaHorizontalPeriod t a = 0 := by
  let : PreconnectedSpace RootHeight := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  obtain ⟨t, hz⟩ := intermediate_value_univ rootRightHeight rootLeftHeight
    root_horizontal_period_continuous ⟨hr.le, hl.le⟩
  have htl : (rootTLower : ℝ) < (t : ℝ) := by
    apply lt_of_le_of_ne t.property.1
    intro he
    have ht : t = rootLeftHeight := Subtype.ext he.symm
    rw [ht] at hz
    linarith
  have htu : (t : ℝ) < (rootTUpper : ℝ) := by
    apply lt_of_le_of_ne t.property.2
    intro he
    have ht : t = rootRightHeight := Subtype.ext he
    rw [ht] at hz
    linarith
  exact ⟨t, rootVerticalA t, ⟨htl, htu⟩, (rootVerticalA_spec t).1, (rootVerticalA_spec t).2, hz⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_common_period_zero_of_endpoint_signs
