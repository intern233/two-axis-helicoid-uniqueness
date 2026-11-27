import TwoAxisHelicoid.PdfFactoredHeatReported
import TwoAxisHelicoid.CompactRootAttachmentSolution
import TwoAxisHelicoid.PdfOriginalSpatialPeriodReduction

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics

/-- The original fifty sharp heat-derivative bounds hold on the branch.
Their largest dyadic upper bound, in row 024, is a uniform bound for the
derivative of the original sigma period on the closed central interval. -/
theorem central_attachment_uniform_derivative {t : ℝ} (ht : t∈Icc (17/20:ℝ) (9/10)) :
    deriv originalPeriodAlong t≤(derivative_024.hPrimeUpper:ℝ) := by
  have dom : t∈Ioo (0:ℝ) ellipticVerticalUpper :=
    ⟨by linarith [ht.1],by linarith [ht.2,ellipticVerticalUpper_location.1]⟩
  obtain ⟨I,member,inside⟩ := partition_covers derivative_partition (by norm_num) (x:=t)
    (by simpa only [Rat.cast_div,Rat.cast_ofNat,Set.mem_Icc] using ht)
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
  have maximum : derivativeData.all (fun row => decide (row.hPrimeUpper≤derivative_024.hPrimeUpper))=true := by decide +kernel
  rw [(originalPeriodAlong_eventuallyEq_actual dom).deriv_eq]
  exact (factored_derivative_table_sharp_upper r hr t inside).trans
    ((Rat.cast_le (K:=ℝ)).mpr (of_decide_eq_true (List.all_eq_true.mp maximum r hr)))

/-- The root and heat attachments alone give exactly one simultaneous
closure of the two spatial generators on the whole central interval. -/
theorem central_attachments_unique_generators (c : ℝ) (hc : c≠0) :
    StrictAntiOn originalPeriodAlong (Icc (17/20:ℝ) (9/10)) ∧
    ∃! p : ℝ × ℝ, p.1∈Icc (17/20:ℝ) (9/10) ∧ ∃ ht : 0<p.1, p.2∈Ioo (0:ℝ) 1 ∧
      ∀ j : Fin 3, (originalCoordinatePeriod p.1 p.2 c ht j).re=0 ∧
        (conjugateCoordinatePeriod p.1 p.2 c ht j).re=0 := by
  have dom : Icc (17/20:ℝ) (9/10)⊆Ioo (0:ℝ) ellipticVerticalUpper := fun t ht =>
    ⟨by linarith [ht.1],by linarith [ht.2,ellipticVerticalUpper_location.1]⟩
  have anti : StrictAntiOn originalPeriodAlong (Icc (17/20:ℝ) (9/10)) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun t ht => (originalPeriodAlong_analyticAt (dom ht)).continuousAt.continuousWithinAt)
      (fun t ht => (central_attachment_uniform_derivative (interior_subset ht)).trans_lt
        (by norm_num [derivative_024]))
  obtain ⟨t,ht,_,_,zero⟩ := compact_root_attachment_contains_period_solution
  have member : t∈Icc (17/20:ℝ) (9/10) :=
    ⟨le_trans (by norm_num [rootTLower]) ht.1.le,ht.2.le.trans (by norm_num [rootTUpper])⟩
  exact ⟨anti,unique_generators_on_of_scalar dom
    ⟨t,⟨member,zero⟩,fun y hy => anti.injOn hy.1 member (hy.2.trans zero.symm)⟩ c hc⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.central_attachment_uniform_derivative
#print axioms TwoAxisHelicoid.PdfVertical.central_attachments_unique_generators
