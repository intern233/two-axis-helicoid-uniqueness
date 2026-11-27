import TwoAxisHelicoid.CompactRootLeftReported
import TwoAxisHelicoid.CompactRootRightReported
import TwoAxisHelicoid.PdfRawTableRootImplication
import TwoAxisHelicoid.OriginalPeriodBridge

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData

theorem compact_root_attachment_signs :
    0 < actualPeriodAlong rootTLower ∧ actualPeriodAlong rootTUpper < 0 := by
  constructor
  · unfold actualPeriodAlong
    rw [show (rootTLower:ℝ)=54139230899/62500000000 by norm_num [rootTLower]]
    exact lt_of_lt_of_le (by norm_num) original_compact_root_left_horizontal_interval.1
  · unfold actualPeriodAlong
    rw [show (rootTUpper:ℝ)=173245538877/200000000000 by norm_num [rootTUpper]]
    exact lt_of_le_of_lt original_compact_root_right_horizontal_interval.2 (by norm_num)

/-- The two horizontal enclosures in the root attachment give a zero of the
actual sigma period by continuity. The uniform vertical columns put that same
zero in the open abscissa interval printed in the attachment. -/
theorem compact_root_attachment_contains_period_solution :
    ∃ t : ℝ, t ∈ Ioo (rootTLower:ℝ) rootTUpper ∧
      verticalA t ∈ Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
          (4409686737857433550400689051219/7427640235712281649394745344000) ∧
      ellipticVerticalPeriod t (verticalA t) = 0 ∧ originalPeriodAlong t = 0 := by
  obtain ⟨left,right⟩ := compact_root_attachment_signs
  have cont := actualPeriodAlong_continuousOn.mono (fun _ h => root_height_in_full_domain h)
  obtain ⟨t,ht,hz⟩ := intermediate_value_Icc'
    (by norm_num [rootTLower,rootTUpper] : (rootTLower:ℝ) ≤ rootTUpper) cont ⟨right.le,left.le⟩
  have hl : (rootTLower:ℝ)<t := lt_of_le_of_ne ht.1 (by rintro rfl; linarith)
  have hu : t<(rootTUpper:ℝ) := lt_of_le_of_ne ht.2 (by rintro rfl; linarith)
  have hd := root_height_in_full_domain ht
  obtain ⟨unit,zero⟩ := verticalA_spec hd
  exact ⟨t,⟨hl,hu⟩,raw_root_uniform_abscissa ht,
    (root_elliptic_vertical_unit_agrees ht.1 unit).trans zero,(originalPeriodAlong_eq_actual hd).trans hz⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compact_root_attachment_contains_period_solution

