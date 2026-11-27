import TwoAxisHelicoid.PdfVerticalBranchRows
import TwoAxisHelicoid.PdfVerticalKeyEquality
import TwoAxisHelicoid.PdfVerticalNegativeRows000
import TwoAxisHelicoid.PdfVerticalNegativeRows001
import TwoAxisHelicoid.PdfVerticalNegativeRows007
import TwoAxisHelicoid.PdfVerticalNegativeRows013
import TwoAxisHelicoid.PdfVerticalNegativeRows019
import TwoAxisHelicoid.PdfVerticalNegativeRows025
import TwoAxisHelicoid.PdfVerticalNegativeRows031
import TwoAxisHelicoid.PdfVerticalNegativeRows037
import TwoAxisHelicoid.PdfVerticalNegativeRows043
import TwoAxisHelicoid.PdfVerticalNegativeRows049
import TwoAxisHelicoid.PdfVerticalNegativeRows055

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def negativeVerticalRows : List VerticalRow :=
  negativeRows000 ++
  negativeRows001 ++
  negativeRows007 ++
  negativeRows013 ++
  negativeRows019 ++
  negativeRows025 ++
  negativeRows031 ++
  negativeRows037 ++
  negativeRows043 ++
  negativeRows049 ++
  negativeRows055

theorem negative_verified_vertical_columns :
    ∀ r∈negativeData, (originalKey r.toSignRow).Sound := by
  apply transfer_vertical_rows (checked:=negativeVerticalRows)
  · simp only [negativeVerticalRows,List.all_append,
      negativeRows000_valid,
      negativeRows001_valid,
      negativeRows007_valid,
      negativeRows013_valid,
      negativeRows019_valid,
      negativeRows025_valid,
      negativeRows031_valid,
      negativeRows037_valid,
      negativeRows043_valid,
      negativeRows049_valid,
      negativeRows055_valid,Bool.and_self]
  · decide +kernel

theorem negative_actual_abscissa_in_reported_interval :
    ∀ r∈negativeData, ∀ t : ℝ, RealMem r.t t →
      (r.a.lower:ℝ)<verticalA t ∧ verticalA t<(r.a.upper:ℝ) :=
  vertical_branches_of_verified_rows negative_partition (by norm_num) (by norm_num)
    negative_verified_vertical_columns

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.negative_verified_vertical_columns
#print axioms TwoAxisHelicoid.PdfVertical.negative_actual_abscissa_in_reported_interval
