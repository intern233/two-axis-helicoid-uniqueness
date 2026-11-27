import TwoAxisHelicoid.PdfHorizontalBlocks1000
import TwoAxisHelicoid.PdfHorizontalBlocks1001
import TwoAxisHelicoid.PdfHorizontalBlocks1005
import TwoAxisHelicoid.PdfHorizontalBlocks1009
import TwoAxisHelicoid.PdfHorizontalBlocks1013
import TwoAxisHelicoid.PdfHorizontalBlocks1019
import TwoAxisHelicoid.PdfHorizontalBlocks1023
import TwoAxisHelicoid.PdfHorizontalBlocks1037
import TwoAxisHelicoid.PdfHorizontalBlocks1041
import TwoAxisHelicoid.PdfHorizontalBlocks1045
import TwoAxisHelicoid.PdfHorizontalBlocks1049
import TwoAxisHelicoid.PdfHorizontalBlocks1053
import TwoAxisHelicoid.PdfHorizontalBlocks1059
import TwoAxisHelicoid.PdfHorizontalBlocks1063
import TwoAxisHelicoid.PdfHorizontalBlocks1077
import TwoAxisHelicoid.PdfHorizontalBlocks1081
import TwoAxisHelicoid.PdfHorizontalBlocks1092
import TwoAxisHelicoid.PdfHorizontalBlocks1096

namespace TwoAxisHelicoid.PdfHorizontal
open CertificateData CertificateSemantics
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def horizontalExistingBlocks : List Block := [
  block1000, block1001, block1002, block1003, block1004, block1005, block1006, block1007, block1008, block1009, block1010, block1011, block1012, block1013, block1016, block1017, block1018, block1019, block1020, block1021, block1022, block1023, block1034, block1035, block1036, block1037, block1038, block1039, block1040, block1041, block1042, block1043, block1044, block1045, block1046, block1047, block1048, block1049, block1050, block1051, block1052, block1053, block1056, block1057, block1058, block1059, block1060, block1061, block1062, block1063, block1074, block1075, block1076, block1077, block1078, block1079, block1080, block1081, block1089, block1090, block1091, block1092, block1093, block1094, block1095, block1096, block1097, block1098]

private theorem blocks_sound : ∀ b∈horizontalExistingBlocks, b.Sound := by
  intro b hb
  simp only [horizontalExistingBlocks,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact block1000_sound
  · exact block1001_sound
  · exact block1002_sound
  · exact block1003_sound
  · exact block1004_sound
  · exact block1005_sound
  · exact block1006_sound
  · exact block1007_sound
  · exact block1008_sound
  · exact block1009_sound
  · exact block1010_sound
  · exact block1011_sound
  · exact block1012_sound
  · exact block1013_sound
  · exact block1016_sound
  · exact block1017_sound
  · exact block1018_sound
  · exact block1019_sound
  · exact block1020_sound
  · exact block1021_sound
  · exact block1022_sound
  · exact block1023_sound
  · exact block1034_sound
  · exact block1035_sound
  · exact block1036_sound
  · exact block1037_sound
  · exact block1038_sound
  · exact block1039_sound
  · exact block1040_sound
  · exact block1041_sound
  · exact block1042_sound
  · exact block1043_sound
  · exact block1044_sound
  · exact block1045_sound
  · exact block1046_sound
  · exact block1047_sound
  · exact block1048_sound
  · exact block1049_sound
  · exact block1050_sound
  · exact block1051_sound
  · exact block1052_sound
  · exact block1053_sound
  · exact block1056_sound
  · exact block1057_sound
  · exact block1058_sound
  · exact block1059_sound
  · exact block1060_sound
  · exact block1061_sound
  · exact block1062_sound
  · exact block1063_sound
  · exact block1074_sound
  · exact block1075_sound
  · exact block1076_sound
  · exact block1077_sound
  · exact block1078_sound
  · exact block1079_sound
  · exact block1080_sound
  · exact block1081_sound
  · exact block1089_sound
  · exact block1090_sound
  · exact block1091_sound
  · exact block1092_sound
  · exact block1093_sound
  · exact block1094_sound
  · exact block1095_sound
  · exact block1096_sound
  · exact block1097_sound
  · exact block1098_sound

theorem existing_rectangles_sound : ∀ b∈horizontalExistingBlocks, b.RectSound := by
  intro b hb
  simp only [horizontalExistingBlocks,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact block1000_rectangle_sound
  · exact block1001_rectangle_sound
  · exact block1002_rectangle_sound
  · exact block1003_rectangle_sound
  · exact block1004_rectangle_sound
  · exact block1005_rectangle_sound
  · exact block1006_rectangle_sound
  · exact block1007_rectangle_sound
  · exact block1008_rectangle_sound
  · exact block1009_rectangle_sound
  · exact block1010_rectangle_sound
  · exact block1011_rectangle_sound
  · exact block1012_rectangle_sound
  · exact block1013_rectangle_sound
  · exact block1016_rectangle_sound
  · exact block1017_rectangle_sound
  · exact block1018_rectangle_sound
  · exact block1019_rectangle_sound
  · exact block1020_rectangle_sound
  · exact block1021_rectangle_sound
  · exact block1022_rectangle_sound
  · exact block1023_rectangle_sound
  · exact block1034_rectangle_sound
  · exact block1035_rectangle_sound
  · exact block1036_rectangle_sound
  · exact block1037_rectangle_sound
  · exact block1038_rectangle_sound
  · exact block1039_rectangle_sound
  · exact block1040_rectangle_sound
  · exact block1041_rectangle_sound
  · exact block1042_rectangle_sound
  · exact block1043_rectangle_sound
  · exact block1044_rectangle_sound
  · exact block1045_rectangle_sound
  · exact block1046_rectangle_sound
  · exact block1047_rectangle_sound
  · exact block1048_rectangle_sound
  · exact block1049_rectangle_sound
  · exact block1050_rectangle_sound
  · exact block1051_rectangle_sound
  · exact block1052_rectangle_sound
  · exact block1053_rectangle_sound
  · exact block1056_rectangle_sound
  · exact block1057_rectangle_sound
  · exact block1058_rectangle_sound
  · exact block1059_rectangle_sound
  · exact block1060_rectangle_sound
  · exact block1061_rectangle_sound
  · exact block1062_rectangle_sound
  · exact block1063_rectangle_sound
  · exact block1074_rectangle_sound
  · exact block1075_rectangle_sound
  · exact block1076_rectangle_sound
  · exact block1077_rectangle_sound
  · exact block1078_rectangle_sound
  · exact block1079_rectangle_sound
  · exact block1080_rectangle_sound
  · exact block1081_rectangle_sound
  · exact block1089_rectangle_sound
  · exact block1090_rectangle_sound
  · exact block1091_rectangle_sound
  · exact block1092_rectangle_sound
  · exact block1093_rectangle_sound
  · exact block1094_rectangle_sound
  · exact block1095_rectangle_sound
  · exact block1096_rectangle_sound
  · exact block1097_rectangle_sound
  · exact block1098_rectangle_sound

def existingRectangleReal := positiveData.filter (fun r =>
  covers true r.toSignRow r.t.lower (horizontalExistingBlocks.filter (matchingRectangle r.toSignRow)))

theorem existing_rectangle_real : existingRectangleReal.length=305 ∧
    ∀ r∈existingRectangleReal, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (pdfDualHorizontalIntegral t a).re := by
  exact ⟨by decide +kernel,positive_rectangular_column_sound horizontalExistingBlocks existing_rectangles_sound true⟩

def existingRectangleImag := positiveData.filter (fun r =>
  covers false r.toSignRow r.t.lower (horizontalExistingBlocks.filter (matchingRectangle r.toSignRow)))

theorem existing_rectangle_imag : existingRectangleImag.length=383 ∧
    ∀ r∈existingRectangleImag, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hImag (pdfDualHorizontalIntegral t a).im := by
  exact ⟨by decide +kernel,positive_rectangular_column_sound horizontalExistingBlocks existing_rectangles_sound false⟩

def existingPositiveReal := positiveData.filter (fun r => covers true r.toSignRow r.t.lower horizontalExistingBlocks)
def existingPositiveImag := positiveData.filter (fun r => covers false r.toSignRow r.t.lower horizontalExistingBlocks)

theorem existing_real_rows : existingPositiveReal.length=345 ∧
    ∀ r∈existingPositiveReal, ∀ t : ℝ, RealMem r.t t → RealMem r.hReal (pdfDualHorizontalIntegral t (verticalA t)).re := by
  exact ⟨by decide +kernel,positive_filtered_column_sound horizontalExistingBlocks blocks_sound true⟩

theorem existing_imag_rows : existingPositiveImag.length=423 ∧
    ∀ r∈existingPositiveImag, ∀ t : ℝ, RealMem r.t t → RealMem r.hImag (pdfDualHorizontalIntegral t (verticalA t)).im := by
  exact ⟨by decide +kernel,positive_filtered_column_sound horizontalExistingBlocks blocks_sound false⟩

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.existing_real_rows
#print axioms TwoAxisHelicoid.PdfHorizontal.existing_imag_rows
#print axioms TwoAxisHelicoid.PdfHorizontal.existing_rectangle_real
#print axioms TwoAxisHelicoid.PdfHorizontal.existing_rectangle_imag
