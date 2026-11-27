import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.PdfHorizontalSimultaneousRows

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics

/-- A row either names a checked entry of the supplemental list, or uses
the existing rectangular bound for both columns. -/
def positiveRowAssignment (direct : List SignRow) (r : CheckedSignRow true (3/10000:ℚ)) :
    Option ℕ → Bool
  | some i => decide (direct[i]?=some r.toSignRow)
  | none => PdfHorizontal.covers true r.toSignRow r.t.lower
      (PdfHorizontal.horizontalExistingBlocks.filter (PdfHorizontal.matchingRectangle r.toSignRow))

def positiveRowAssignments (direct : List SignRow) :
    List (CheckedSignRow true (3/10000:ℚ)) → List (Option ℕ) → Bool
  | [],[] => true
  | r::rs,i::is => positiveRowAssignment direct r i && positiveRowAssignments direct rs is
  | _,_ => false

theorem positive_row_assignment_member {direct : List SignRow}
    {rows : List (CheckedSignRow true (3/10000:ℚ))} {indices : List (Option ℕ)}
    (ok : positiveRowAssignments direct rows indices=true) {r : CheckedSignRow true (3/10000:ℚ)}
    (hr : r∈rows) :
    r.toSignRow∈direct ∨ PdfHorizontal.covers true r.toSignRow r.t.lower
      (PdfHorizontal.horizontalExistingBlocks.filter (PdfHorizontal.matchingRectangle r.toSignRow))=true := by
  induction rows generalizing indices with
  | nil => simp at hr
  | cons head rest ih =>
    cases indices with
    | nil => simp [positiveRowAssignments] at ok
    | cons index tail =>
      obtain ⟨first,remaining⟩ := Bool.and_eq_true_iff.mp ok
      rcases List.mem_cons.mp hr with same|member
      · subst r
        cases index with
        | none => exact Or.inr first
        | some i => exact Or.inl (List.mem_of_getElem? (of_decide_eq_true first))
      · exact ih remaining member

theorem positive_original_rows_of_assignments {direct : List SignRow} {indices : List (Option ℕ)}
    (good : OriginalHorizontalRowsSound true direct)
    (ok : positiveRowAssignments direct positiveData indices=true) :
    OriginalHorizontalRowsSound true (positiveData.map CheckedSignRow.toSignRow) := by
  intro r member t a ht ha
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp member
  rcases positive_row_assignment_member ok hs with known|old
  · exact good _ known t a ht ha
  · exact PdfHorizontal.source_rectangles_both_columns.2 s (List.mem_filter.mpr ⟨hs,old⟩) t a ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positive_original_rows_of_assignments
