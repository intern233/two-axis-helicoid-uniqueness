import TwoAxisHelicoid.PdfVerticalBranchRows
import TwoAxisHelicoid.PdfVerticalKeyEquality
import TwoAxisHelicoid.PdfVerticalPositiveRows000
import TwoAxisHelicoid.PdfVerticalPositiveRows001
import TwoAxisHelicoid.PdfVerticalPositiveRows025
import TwoAxisHelicoid.PdfVerticalPositiveRows049
import TwoAxisHelicoid.PdfVerticalPositiveRows073
import TwoAxisHelicoid.PdfVerticalPositiveRows097
import TwoAxisHelicoid.PdfVerticalPositiveRows121
import TwoAxisHelicoid.PdfVerticalPositiveRows145
import TwoAxisHelicoid.PdfVerticalPositiveRows169
import TwoAxisHelicoid.PdfVerticalPositiveRows193
import TwoAxisHelicoid.PdfVerticalPositiveRows217
import TwoAxisHelicoid.PdfVerticalPositiveRows241
import TwoAxisHelicoid.PdfVerticalPositiveRows265
import TwoAxisHelicoid.PdfVerticalPositiveRows289
import TwoAxisHelicoid.PdfVerticalPositiveRows313
import TwoAxisHelicoid.PdfVerticalPositiveRows337
import TwoAxisHelicoid.PdfVerticalPositiveRows361
import TwoAxisHelicoid.PdfVerticalPositiveRows385
import TwoAxisHelicoid.PdfVerticalPositiveRows409
import TwoAxisHelicoid.PdfVerticalPositiveRows433
import TwoAxisHelicoid.PdfVerticalPositiveRows457
import TwoAxisHelicoid.PdfVerticalPositiveRows481
import TwoAxisHelicoid.PdfVerticalPositiveRows505
import TwoAxisHelicoid.PdfVerticalPositiveRows529
import TwoAxisHelicoid.PdfVerticalPositiveRows553

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def positiveVerticalRows : List VerticalRow :=
  positiveRows000 ++
  positiveRows001 ++
  positiveRows025 ++
  positiveRows049 ++
  positiveRows073 ++
  positiveRows097 ++
  positiveRows121 ++
  positiveRows145 ++
  positiveRows169 ++
  positiveRows193 ++
  positiveRows217 ++
  positiveRows241 ++
  positiveRows265 ++
  positiveRows289 ++
  positiveRows313 ++
  positiveRows337 ++
  positiveRows361 ++
  positiveRows385 ++
  positiveRows409 ++
  positiveRows433 ++
  positiveRows457 ++
  positiveRows481 ++
  positiveRows505 ++
  positiveRows529 ++
  positiveRows553

theorem positive_verified_vertical_columns :
    ∀ r∈positiveData, (originalKey r.toSignRow).Sound := by
  apply transfer_vertical_rows (checked:=positiveVerticalRows)
  · simp only [positiveVerticalRows,List.all_append,
      positiveRows000_valid,
      positiveRows001_valid,
      positiveRows025_valid,
      positiveRows049_valid,
      positiveRows073_valid,
      positiveRows097_valid,
      positiveRows121_valid,
      positiveRows145_valid,
      positiveRows169_valid,
      positiveRows193_valid,
      positiveRows217_valid,
      positiveRows241_valid,
      positiveRows265_valid,
      positiveRows289_valid,
      positiveRows313_valid,
      positiveRows337_valid,
      positiveRows361_valid,
      positiveRows385_valid,
      positiveRows409_valid,
      positiveRows433_valid,
      positiveRows457_valid,
      positiveRows481_valid,
      positiveRows505_valid,
      positiveRows529_valid,
      positiveRows553_valid,Bool.and_self]
  · decide +kernel

theorem positive_actual_abscissa_in_reported_interval :
    ∀ r∈positiveData, ∀ t : ℝ, RealMem r.t t →
      (r.a.lower:ℝ)<verticalA t ∧ verticalA t<(r.a.upper:ℝ) :=
  vertical_branches_of_verified_rows positive_partition (by norm_num) (by norm_num)
    positive_verified_vertical_columns

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positive_verified_vertical_columns
#print axioms TwoAxisHelicoid.PdfVertical.positive_actual_abscissa_in_reported_interval
