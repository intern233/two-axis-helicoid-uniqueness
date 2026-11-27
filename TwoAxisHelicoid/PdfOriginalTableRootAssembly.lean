import TwoAxisHelicoid.CompactRootAttachmentSolution
import TwoAxisHelicoid.PdfHorizontalIntegral
import TwoAxisHelicoid.PdfVerticalNegativeReported
import TwoAxisHelicoid.PdfEndpointReportedVertical

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics

/-- The original horizontal tables act on the actual complex paths. The
negative rows restrict to the true vertical branch using their own original
abscissa brackets. The precise root signs come from the root attachment. -/
theorem original_table_columns_imply_sigma_root
    (positive : ∀ r∈positiveData, ∀ t : ℝ, RealMem r.t t → RealMem r.hReal (actualPeriodAlong t))
    (negative : ∀ r∈negativeData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (pdfPrimalHorizontalIntegral t a).re)
    (heat : ∀ r∈derivativeData, ∀ t : ℝ, RealMem r.t t → deriv actualPeriodAlong t≤(r.hPrimeUpper:ℝ))
    (edge : ∀ r∈endpointData, ∀ t a : ℝ, (7/5:ℝ)≤t → t≤141/100 →
      RealMem r.a a → thetaHorizontalPeriod t a≤(r.hUpper:ℝ)) :
    (∃! t : ℝ, t∈Ioo (0:ℝ) ellipticVerticalUpper ∧ originalPeriodAlong t=0) ∧
    ∀ t∈Ioo (0:ℝ) ellipticVerticalUpper, originalPeriodAlong t=0 →
      t∈Ioo (rootTLower:ℝ) rootTUpper ∧
      verticalA t∈Ioo (4409686737850678150959633307219/7427640235712281649394745344000:ℝ)
        (4409686737857433550400689051219/7427640235712281649394745344000) ∧
      deriv originalPeriodAlong t< -8 := by
  have test : negativeData.all (fun r => decide (0<r.t.lower))=true := by decide +kernel
  have branch : ∀ r∈negativeData, ∀ t : ℝ, RealMem r.t t → RealMem r.hReal (actualPeriodAlong t) := by
    intro r hr t ht
    obtain ⟨al,au⟩ := negative_actual_abscissa_in_reported_interval r hr t ht
    have tp := ((Rat.cast_pos (K:=ℝ)).mpr (of_decide_eq_true (List.all_eq_true.mp test r hr))).trans_le ht.1
    have value := negative r hr t (verticalA t) ht ⟨al.le,au.le⟩
    rw [pdf_primal_horizontal_integral_real tp,Complex.ofReal_re] at value
    exact value
  have all := raw_tables_period_hypotheses positive branch heat edge (fun _ => original_right_cut_locates_branch)
  obtain ⟨t,⟨domain,zero⟩,only⟩ := existsUnique_period_zero_of_hypotheses all
  obtain ⟨left,right⟩ := compact_root_attachment_signs
  constructor
  · refine ⟨t,⟨domain,(originalPeriodAlong_eq_actual domain).trans zero⟩,?_⟩
    intro s hs
    exact only s ⟨hs.1,(originalPeriodAlong_eq_actual hs.1).symm.trans hs.2⟩
  · intro s hs eqn
    rw [(originalPeriodAlong_eventuallyEq_actual hs).deriv_eq]
    exact raw_root_signs_give_location all heat left right hs ((originalPeriodAlong_eq_actual hs).symm.trans eqn)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_table_columns_imply_sigma_root
