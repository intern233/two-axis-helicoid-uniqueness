import TwoAxisHelicoid.PdfAllAdmissibleSpatialPeriods
import TwoAxisHelicoid.PdfAllOriginalPeriodColumns
import TwoAxisHelicoid.PdfOriginalTableRootAssembly

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics

/-- Proof of Theorem 10.1 along the source attachment route. The four
tables provide the sign and derivative bounds, and the root attachment
supplies the end signs and the strict abscissa localization. -/
theorem actual_period_root_from_original_attachments :
    (∃! t : ℝ, t∈Ioo (0:ℝ) ellipticVerticalUpper ∧ originalPeriodAlong t=0) ∧
    ∀ t∈Ioo (0:ℝ) ellipticVerticalUpper, originalPeriodAlong t=0 →
      t∈Ioo (rootTLower:ℝ) rootTUpper ∧
      verticalA t∈Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
        (4409686737857433550400689051219/7427640235712281649394745344000) ∧
      deriv originalPeriodAlong t< -8 := by
  obtain ⟨_,positive,negative,heat,edge⟩ := original_period_column_tables
  exact original_table_columns_imply_sigma_root (fun r hr t ht => (positive r hr t ht).1)
    (fun r hr t a ht ha => (negative r hr t a ht ha).1) heat edge

theorem original_attachments_unique_spatial_generators (c : ℝ) (hc : c≠0) :
    ∃! p : ℝ × ℝ, p.1∈Ioo (0:ℝ) ellipticVerticalUpper ∧ ∃ ht : 0<p.1, p.2∈Ioo (0:ℝ) 1 ∧
      ∀ j : Fin 3, (originalCoordinatePeriod p.1 p.2 c ht j).re=0 ∧
        (conjugateCoordinatePeriod p.1 p.2 c ht j).re=0 :=
  unique_generators_on_of_scalar (fun _ h => h) actual_period_root_from_original_attachments.1 c hc

/-- The analytic cutoff follows from closure itself. This is the unique pair
for the original spatial periods over their entire positive-height domain. -/
theorem original_attachments_unique_at_all_positive_heights (c : ℝ) (hc : c≠0) :
    ∃! p : ℝ × ℝ, ∃ ht : 0<p.1, p.2∈Ioo (0:ℝ) 1 ∧ ∀ j : Fin 3,
      (originalCoordinatePeriod p.1 p.2 c ht j).re=0 ∧
      (conjugateCoordinatePeriod p.1 p.2 c ht j).re=0 :=
  unique_positive_generators_of_branch_root actual_period_root_from_original_attachments.1 c hc

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.actual_period_root_from_original_attachments
#print axioms TwoAxisHelicoid.PdfVertical.original_attachments_unique_spatial_generators
#print axioms TwoAxisHelicoid.PdfVertical.original_attachments_unique_at_all_positive_heights
