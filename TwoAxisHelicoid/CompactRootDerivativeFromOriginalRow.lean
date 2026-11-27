import TwoAxisHelicoid.PdfOriginalSpatialPeriodReduction
import TwoAxisHelicoid.CompactRootAttachmentSolution
import TwoAxisHelicoid.PdfFactoredHeatRow016
import TwoAxisHelicoid.PdfOriginalDerivativeAbscissas

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics

/-- Row 016 of the original derivative table covers every height in the
closed root interval, including both endpoints of the bisection. -/
theorem compact_root_derivative_from_row_016 {t : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper) :
    deriv originalPeriodAlong t ≤ (derivative_016.hPrimeUpper:ℝ) := by
  have row : derivative_016∈derivativeData :=
    List.getElem_mem (l:=derivativeData) (n:=16) (by decide)
  have tb : RealMem derivative_016.t t :=
    ⟨le_trans (by norm_num [derivative_016,rootTLower]) ht.1,
      ht.2.trans (by norm_num [derivative_016,rootTUpper])⟩
  obtain ⟨al,au⟩ := original_derivative_abscissa_rows _ row _ tb
  have dom := root_height_in_full_domain ht
  rw [(originalPeriodAlong_eventuallyEq_actual dom).deriv_eq, ← reportedHeatPeriod_branch dom]
  exact factored_original_heat_016 tb ⟨al.le,au.le⟩

/-- On the root attachment's own closed interval the original sigma period
is strictly decreasing. The actual root is simple, with the dyadic bound
from the original row, and is unique even among the closed endpoints. -/
theorem compact_root_attachment_unique_simple :
    StrictAntiOn originalPeriodAlong (Icc (rootTLower:ℝ) rootTUpper) ∧
    (∃! t : ℝ, t ∈ Icc (rootTLower:ℝ) rootTUpper ∧ originalPeriodAlong t=0) ∧
    ∀ t∈Icc (rootTLower:ℝ) rootTUpper, deriv originalPeriodAlong t < -8 := by
  have neg (t : ℝ) (ht : t∈Icc (rootTLower:ℝ) rootTUpper) : deriv originalPeriodAlong t < -8 :=
    (compact_root_derivative_from_row_016 ht).trans_lt (by norm_num [derivative_016])
  have cont : ContinuousOn originalPeriodAlong (Icc (rootTLower:ℝ) rootTUpper) :=
    fun _ ht => (originalPeriodAlong_analyticAt (root_height_in_full_domain ht)).continuousAt.continuousWithinAt
  have anti : StrictAntiOn originalPeriodAlong (Icc (rootTLower:ℝ) rootTUpper) :=
    strictAntiOn_of_deriv_neg (convex_Icc _ _) cont
      (fun t ht => (neg t (interior_subset ht)).trans (by norm_num))
  obtain ⟨t,ht,_,_,hz⟩ := compact_root_attachment_contains_period_solution
  have hc : t∈Icc (rootTLower:ℝ) rootTUpper := ⟨ht.1.le,ht.2.le⟩
  exact ⟨anti,⟨t,⟨hc,hz⟩,fun y hy => anti.injOn hy.1 hc (hy.2.trans hz.symm)⟩,neg⟩

theorem compact_root_attachment_unique_generators (c : ℝ) (hc : c≠0) :
    ∃! p : ℝ × ℝ, p.1∈Icc (rootTLower:ℝ) rootTUpper ∧ ∃ ht : 0<p.1, p.2∈Ioo (0:ℝ) 1 ∧
      ∀ j : Fin 3, (originalCoordinatePeriod p.1 p.2 c ht j).re=0 ∧
        (conjugateCoordinatePeriod p.1 p.2 c ht j).re=0 :=
  unique_generators_on_of_scalar (fun _ h => root_height_in_full_domain h)
    compact_root_attachment_unique_simple.2.1 c hc

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.compact_root_attachment_unique_simple

#print axioms TwoAxisHelicoid.PdfVertical.compact_root_attachment_unique_generators
