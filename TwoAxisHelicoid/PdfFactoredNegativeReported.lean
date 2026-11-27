import TwoAxisHelicoid.PdfFactoredNegativeRow000
import TwoAxisHelicoid.PdfFactoredNegativeRow001
import TwoAxisHelicoid.PdfShortNegativeRows002
import TwoAxisHelicoid.PdfShortNegativeRows006
import TwoAxisHelicoid.PdfShortNegativeRows008
import TwoAxisHelicoid.PdfShortNegativeRows012
import TwoAxisHelicoid.PdfShortNegativeRows016
import TwoAxisHelicoid.PdfShortNegativeRows020
import TwoAxisHelicoid.PdfShortNegativeRows024
import TwoAxisHelicoid.PdfShortNegativeRows028
import TwoAxisHelicoid.PdfShortNegativeRows032
import TwoAxisHelicoid.PdfShortNegativeRows036
import TwoAxisHelicoid.PdfShortNegativeRows039
import TwoAxisHelicoid.PdfShortNegativeRows040
import TwoAxisHelicoid.PdfShortNegativeRows042
import TwoAxisHelicoid.PdfShortNegativeRows044
import TwoAxisHelicoid.PdfShortNegativeRows046
import TwoAxisHelicoid.PdfShortNegativeRows048
import TwoAxisHelicoid.PdfShortNegativeRows050
import TwoAxisHelicoid.PdfShortNegativeRows052
import TwoAxisHelicoid.PdfShortNegativeRows054
import TwoAxisHelicoid.PdfShortNegativeRows056
import TwoAxisHelicoid.PdfShortNegativeRows058
import TwoAxisHelicoid.PdfHorizontalIntegral

namespace TwoAxisHelicoid.PdfVertical
open Set CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem factored_negative_table_real : ∀ r∈negativeData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem r.hReal (thetaHorizontalPeriod t a) := by
  intro r hr t a tb ab
  simp only [negativeData,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact factored_original_negative_000 tb ab
  · exact factored_original_negative_001 tb ab
  · exact short_original_negative_002 tb ab
  · exact short_original_negative_003 tb ab
  · exact short_original_negative_004 tb ab
  · exact short_original_negative_005 tb ab
  · exact short_original_negative_006 tb ab
  · exact short_original_negative_007 tb ab
  · exact short_original_negative_008 tb ab
  · exact short_original_negative_009 tb ab
  · exact short_original_negative_010 tb ab
  · exact short_original_negative_011 tb ab
  · exact short_original_negative_012 tb ab
  · exact short_original_negative_013 tb ab
  · exact short_original_negative_014 tb ab
  · exact short_original_negative_015 tb ab
  · exact short_original_negative_016 tb ab
  · exact short_original_negative_017 tb ab
  · exact short_original_negative_018 tb ab
  · exact short_original_negative_019 tb ab
  · exact short_original_negative_020 tb ab
  · exact short_original_negative_021 tb ab
  · exact short_original_negative_022 tb ab
  · exact short_original_negative_023 tb ab
  · exact short_original_negative_024 tb ab
  · exact short_original_negative_025 tb ab
  · exact short_original_negative_026 tb ab
  · exact short_original_negative_027 tb ab
  · exact short_original_negative_028 tb ab
  · exact short_original_negative_029 tb ab
  · exact short_original_negative_030 tb ab
  · exact short_original_negative_031 tb ab
  · exact short_original_negative_032 tb ab
  · exact short_original_negative_033 tb ab
  · exact short_original_negative_034 tb ab
  · exact short_original_negative_035 tb ab
  · exact short_original_negative_036 tb ab
  · exact short_original_negative_037 tb ab
  · exact short_original_negative_038 tb ab
  · exact short_original_negative_039 tb ab
  · exact short_original_negative_040 tb ab
  · exact short_original_negative_041 tb ab
  · exact short_original_negative_042 tb ab
  · exact short_original_negative_043 tb ab
  · exact short_original_negative_044 tb ab
  · exact short_original_negative_045 tb ab
  · exact short_original_negative_046 tb ab
  · exact short_original_negative_047 tb ab
  · exact short_original_negative_048 tb ab
  · exact short_original_negative_049 tb ab
  · exact short_original_negative_050 tb ab
  · exact short_original_negative_051 tb ab
  · exact short_original_negative_052 tb ab
  · exact short_original_negative_053 tb ab
  · exact short_original_negative_054 tb ab
  · exact short_original_negative_055 tb ab
  · exact short_original_negative_056 tb ab
  · exact short_original_negative_057 tb ab
  · exact short_original_negative_058 tb ab

theorem factored_negative_table_horizontal_columns :
    ∀ r∈negativeData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (pdfPrimalHorizontalIntegral t a).re ∧ RealMem r.hImag (pdfPrimalHorizontalIntegral t a).im := by
  intro r hr t a tb ab
  have arith : negativeData.all (fun v => decide (0<v.t.lower))=true := by decide +kernel
  have ht := ((Rat.cast_pos (K:=ℝ)).mpr (of_decide_eq_true (List.all_eq_true.mp arith r hr))).trans_le tb.1
  exact ⟨by simpa only [pdf_primal_horizontal_integral_real ht,Complex.ofReal_re] using factored_negative_table_real r hr t a tb ab,
    negative_table_actual_imaginary_intervals r hr t a tb⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factored_negative_table_horizontal_columns
