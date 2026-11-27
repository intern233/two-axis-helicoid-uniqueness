import TwoAxisHelicoid.PdfEndpointHorizontalReported
import TwoAxisHelicoid.PdfEndpointReportedVertical
import TwoAxisHelicoid.PdfOriginalSpatialPeriodReduction
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics

/-- Row 005 has the largest dyadic upper bound of all ten rows. This
bound holds on the whole closed right-hand rectangle, including a=1. -/
theorem right_attachment_uniform_rectangle {t a : ℝ}
    (ht : t∈Icc (7/5:ℝ) (141/100)) (ha : a∈Icc (9/10:ℝ) 1) :
    thetaHorizontalPeriod t a≤(endpoint_005.hUpper:ℝ) := by
  obtain ⟨I,member,inside⟩ := partition_covers endpoint_partition (by norm_num) (x:=a)
    (by simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,div_one,Set.mem_Icc] using ha)
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
  have maximum : endpointData.all (fun row => decide (row.hUpper≤endpoint_005.hUpper))=true := by decide +kernel
  exact (original_endpoint_ten_horizontal_upper_bounds r hr t a ht.1 ht.2 inside).trans
    ((Rat.cast_le (K:=ℝ)).mpr (of_decide_eq_true (List.all_eq_true.mp maximum r hr)))

/-- The endpoint attachment excludes closure on both spatial generators
for every height at least 7/5. Beyond the admissible domain the vertical
equation itself already excludes a solution. -/
theorem right_attachment_excludes_closed_generators {t a c : ℝ} (ht : (7/5:ℝ)≤t)
    (hp : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0) :
    ∃ j : Fin 3, (originalCoordinatePeriod t a c hp j).re≠0 ∨
      (conjugateCoordinatePeriod t a c hp j).re≠0 := by
  by_contra! allClosed
  obtain ⟨upper,ab,zero⟩ := (spatial_generators_iff_original_scalar hp ha hc).mp allClosed
  have limit := ellipticVerticalUpper_location
  have tu : t≤141/100 := upper.le.trans (limit.2.le.trans (by norm_num))
  obtain ⟨lo,hi⟩ := original_right_cut_locates_branch ht tu upper
  have negative := (right_attachment_uniform_rectangle ⟨ht,tu⟩ ⟨lo.le,hi.le⟩).trans_lt
    (by norm_num [endpoint_005] : (endpoint_005.hUpper:ℝ)<0)
  have closed : thetaHorizontalPeriod t (verticalA t)=0 :=
    (originalPeriodAlong_eq_actual ⟨hp,upper⟩).symm.trans zero
  exact negative.ne closed

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.right_attachment_uniform_rectangle
#print axioms TwoAxisHelicoid.PdfVertical.right_attachment_excludes_closed_generators
