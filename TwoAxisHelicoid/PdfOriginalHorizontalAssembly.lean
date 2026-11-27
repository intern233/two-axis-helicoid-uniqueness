import TwoAxisHelicoid.PdfHorizontalGroupedTransfer
import TwoAxisHelicoid.PdfVerticalKeyEquality
import TwoAxisHelicoid.PdfHorizontalRowTransfer

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics

deriving instance DecidableEq for CertificateData.SignRow

def OriginalHorizontalRowsSound (dual : Bool) (rows : List SignRow) : Prop :=
  ∀ r∈rows, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
    RealMem r.hReal (sourceHorizontalIntegral dual t a).re ∧
      RealMem r.hImag (sourceHorizontalIntegral dual t a).im

theorem original_horizontal_rows_append {side : Bool} {a b : List SignRow}
    (ha : OriginalHorizontalRowsSound side a) (hb : OriginalHorizontalRowsSound side b) :
    OriginalHorizontalRowsSound side (a++b) := by
  intro r h
  exact (List.mem_append.mp h).elim (ha r) (hb r)

/-- A row may be covered by a source-shaped complex rectangle or by
two already certified columns of the real chord transfer. Both cases
establish the two intervals for every point of its full parameter box. -/
theorem positive_original_rows_of_coverage {direct : List SignRow} (good : OriginalHorizontalRowsSound true direct)
    (blocks : List PdfHorizontal.Block) (each : ∀ b∈blocks,b.RectSound)
    (all : positiveData.all (fun r => decide (r.toSignRow∈direct) ||
      (PdfHorizontal.covers true r.toSignRow r.t.lower (blocks.filter (PdfHorizontal.matchingRectangle r.toSignRow)) &&
        PdfHorizontal.covers false r.toSignRow r.t.lower (blocks.filter (PdfHorizontal.matchingRectangle r.toSignRow))))=true) :
    OriginalHorizontalRowsSound true (positiveData.map CheckedSignRow.toSignRow) := by
  intro r hr t a ht ha
  obtain ⟨s,member,rfl⟩ := List.mem_map.mp hr
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp all s member) with directRow | pq
  · exact good _ (of_decide_eq_true directRow) t a ht ha
  · obtain ⟨pr,pi⟩ := Bool.and_eq_true_iff.mp pq
    exact ⟨PdfHorizontal.positive_rectangular_column_sound blocks each true s (List.mem_filter.mpr ⟨member,pr⟩) t a ht ha,
      PdfHorizontal.positive_rectangular_column_sound blocks each false s (List.mem_filter.mpr ⟨member,pi⟩) t a ht ha⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positive_original_rows_of_coverage
