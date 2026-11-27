import TwoAxisHelicoid.PdfVerticalPositiveReported
import TwoAxisHelicoid.PdfVerticalNegativeReported
import TwoAxisHelicoid.PdfDerivativeVerticalReported
import TwoAxisHelicoid.PdfOriginalDerivativeAbscissas

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics Set

/-- The vertical columns are intervals for the actual source-normalized
vertical function at both proposed abscissas. The bracket is strict
for every real time in the corresponding closed input interval. -/
def SignTableVerticalSound {b : Bool} {margin : ℚ} (rs : List (CheckedSignRow b margin)) : Prop :=
  (∀ r∈rs, (originalKey r.toSignRow).Sound) ∧
  ∀ r∈rs, ∀ t : ℝ, RealMem r.t t → verticalA t∈Ioo (r.a.lower:ℝ) (r.a.upper:ℝ)

/-- All 667 original time rows, with their exact function enclosures
and actual root brackets. The derivative table uses one-sided bounds. -/
theorem original_all_vertical_tables :
    positiveData.length+negativeData.length+derivativeData.length=667 ∧
    SignTableVerticalSound positiveData ∧ SignTableVerticalSound negativeData ∧
    ∀ r∈derivativeData, ∀ t : ℝ, RealMem r.t t →
      (r.verticalLower:ℝ)≤(thetaG t (r.a.lower:ℝ)).re ∧
      (thetaG t (r.a.upper:ℝ)).re≤(r.verticalUpper:ℝ) ∧
      verticalA t∈Ioo (r.a.lower:ℝ) (r.a.upper:ℝ) := by
  refine ⟨by rw [positive_count,negative_count,derivative_count],
    ⟨positive_verified_vertical_columns,positive_actual_abscissa_in_reported_interval⟩,
    ⟨negative_verified_vertical_columns,negative_actual_abscissa_in_reported_interval⟩,?_⟩
  intro r hr t ht
  obtain ⟨low,high⟩ := derivative_table_actual_vertical_bounds r hr t ht
  exact ⟨low,high,original_derivative_abscissa_rows r hr t ht⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.original_all_vertical_tables

