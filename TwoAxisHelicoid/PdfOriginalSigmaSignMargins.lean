import TwoAxisHelicoid.PdfOriginalExactSignMargins
import TwoAxisHelicoid.PdfPositiveCompleteColumns
import TwoAxisHelicoid.PdfOriginalPositivePeriodBridge
import TwoAxisHelicoid.PdfVerticalPositiveReported
import TwoAxisHelicoid.PdfFactoredNegativeReported
import TwoAxisHelicoid.PdfVerticalNegativeReported
import TwoAxisHelicoid.OriginalPeriodBridge

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics

/-- The actual sigma period has the exact reported uniform margins. The
second table uses its original real integration path, and the first uses
the dual path evaluated at the actual vertical root. -/
theorem original_attachment_sigma_sign_margins :
    (∀ t∈Icc (1/8:ℝ) (17/20), (originalPositiveMargin:ℝ)≤originalPeriodAlong t) ∧
    ∀ t∈Icc (9/10:ℝ) (7/5), originalPeriodAlong t≤ -(originalNegativeMargin:ℝ) := by
  have positive := positive_table_branch_of_columns all_original_positive_horizontal_columns
    positive_actual_abscissa_in_reported_interval
  have bounds := original_summary_margins_of_enclosures actualPeriodAlong
    (fun r hr t ht => (positive r hr t ht).1) (by
      intro r hr t ht
      obtain ⟨lo,hi⟩ := negative_actual_abscissa_in_reported_interval r hr t ht
      exact factored_negative_table_real r hr t (verticalA t) ht ⟨lo.le,hi.le⟩)
  have eqn {t : ℝ} (lo : 0<t) (hi : t≤7/5) : originalPeriodAlong t=actualPeriodAlong t :=
    originalPeriodAlong_eq_actual ⟨lo,by linarith [ellipticVerticalUpper_location.1]⟩
  constructor
  · intro t ht
    rw [eqn (by linarith [ht.1]) (by linarith [ht.2])]
    exact bounds.1 t ht
  · intro t ht
    rw [eqn (by linarith [ht.1]) ht.2]
    exact bounds.2 t ht

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_attachment_sigma_sign_margins

