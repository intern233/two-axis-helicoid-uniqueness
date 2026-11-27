import TwoAxisHelicoid.PdfFactoredHeatRow000
import TwoAxisHelicoid.PdfFactoredHeatRow001
import TwoAxisHelicoid.PdfFactoredHeatBatch002
import TwoAxisHelicoid.PdfFactoredHeatBatch007
import TwoAxisHelicoid.PdfFactoredHeatBatch012
import TwoAxisHelicoid.PdfFactoredHeatRow016
import TwoAxisHelicoid.PdfFactoredHeatBatch018
import TwoAxisHelicoid.PdfFactoredHeatBatch023
import TwoAxisHelicoid.PdfFactoredHeatBatch028
import TwoAxisHelicoid.PdfFactoredHeatBatch033
import TwoAxisHelicoid.PdfFactoredHeatBatch038
import TwoAxisHelicoid.PdfFactoredHeatBatch043
import TwoAxisHelicoid.PdfFactoredHeatBatch048
import TwoAxisHelicoid.PdfOriginalDerivativeAbscissas
import TwoAxisHelicoid.RangePeriodBounds

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factored_horizontal_heat_table : ∀ r∈derivativeData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → reportedHeatPeriod t a≤(r.hPrimeUpper:ℝ) := by
  intro r member t a tb ab
  simp only [derivativeData,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact factored_original_heat_000 tb ab
  · exact factored_original_heat_001 tb ab
  · exact factored_original_heat_002 tb ab
  · exact factored_original_heat_003 tb ab
  · exact factored_original_heat_004 tb ab
  · exact factored_original_heat_005 tb ab
  · exact factored_original_heat_006 tb ab
  · exact factored_original_heat_007 tb ab
  · exact factored_original_heat_008 tb ab
  · exact factored_original_heat_009 tb ab
  · exact factored_original_heat_010 tb ab
  · exact factored_original_heat_011 tb ab
  · exact factored_original_heat_012 tb ab
  · exact factored_original_heat_013 tb ab
  · exact factored_original_heat_014 tb ab
  · exact factored_original_heat_015 tb ab
  · exact factored_original_heat_016 tb ab
  · exact factored_original_heat_017 tb ab
  · exact factored_original_heat_018 tb ab
  · exact factored_original_heat_019 tb ab
  · exact factored_original_heat_020 tb ab
  · exact factored_original_heat_021 tb ab
  · exact factored_original_heat_022 tb ab
  · exact factored_original_heat_023 tb ab
  · exact factored_original_heat_024 tb ab
  · exact factored_original_heat_025 tb ab
  · exact factored_original_heat_026 tb ab
  · exact factored_original_heat_027 tb ab
  · exact factored_original_heat_028 tb ab
  · exact factored_original_heat_029 tb ab
  · exact factored_original_heat_030 tb ab
  · exact factored_original_heat_031 tb ab
  · exact factored_original_heat_032 tb ab
  · exact factored_original_heat_033 tb ab
  · exact factored_original_heat_034 tb ab
  · exact factored_original_heat_035 tb ab
  · exact factored_original_heat_036 tb ab
  · exact factored_original_heat_037 tb ab
  · exact factored_original_heat_038 tb ab
  · exact factored_original_heat_039 tb ab
  · exact factored_original_heat_040 tb ab
  · exact factored_original_heat_041 tb ab
  · exact factored_original_heat_042 tb ab
  · exact factored_original_heat_043 tb ab
  · exact factored_original_heat_044 tb ab
  · exact factored_original_heat_045 tb ab
  · exact factored_original_heat_046 tb ab
  · exact factored_original_heat_047 tb ab
  · exact factored_original_heat_048 tb ab
  · exact factored_original_heat_049 tb ab

theorem factored_derivative_table_sharp_upper :
    ∀ r∈derivativeData, ∀ t : ℝ, RealMem r.t t → deriv actualPeriodAlong t≤(r.hPrimeUpper:ℝ) := by
  intro r member t tb
  have domainCheck : derivativeData.all (fun e => decide ((17/20:ℚ)≤e.t.lower ∧ e.t.upper≤9/10))=true := by decide +kernel
  obtain ⟨tl,tu⟩ := of_decide_eq_true (List.all_eq_true.mp domainCheck r member)
  have lo := (Rat.cast_le (K:=ℝ)).mpr tl
  have hi := (Rat.cast_le (K:=ℝ)).mpr tu
  push_cast at lo hi
  have ht : t∈Ioo (0:ℝ) ellipticVerticalUpper := ⟨by linarith [tb.1],by linarith [tb.2,ellipticVerticalUpper_location.1]⟩
  have interior := original_derivative_abscissa_rows r member t tb
  rw [← reportedHeatPeriod_branch ht]
  exact factored_horizontal_heat_table r member t (verticalA t) tb ⟨interior.1.le,interior.2.le⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_derivative_table_sharp_upper
