import TwoAxisHelicoid.PdfOriginalHorizontalAssembly
import TwoAxisHelicoid.FullPeriodBranch

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics

/-- Transfer the reported positive-table complex integral to the real
horizontal period on every point of every original rectangle. -/
theorem positive_table_period_of_columns
    (columns : OriginalHorizontalRowsSound true (positiveData.map CheckedSignRow.toSignRow)) :
    ∀ r∈positiveData, ∀ t a : ℝ, RealMem r.t t → RealMem r.a a →
      RealMem r.hReal (thetaHorizontalPeriod t a) ∧ 3/10000<thetaHorizontalPeriod t a := by
  have check : positiveData.all (fun r => decide (0<r.t.lower ∧ r.t.upper≤7/5))=true := by decide +kernel
  intro r hr t a ht ha
  have bound := (columns r.toSignRow (List.mem_map_of_mem hr) t a ht ha).1
  change RealMem r.hReal (pdfDualHorizontalIntegral t a).re at bound
  obtain ⟨low,up⟩ := of_decide_eq_true (List.all_eq_true.mp check r hr)
  have tp := (Rat.cast_pos.mpr low).trans_le ht.1
  have tU := (Rat.cast_le (K:=ℝ)).mpr up
  push_cast at tU
  have tu : t≤7/5 := ht.2.trans tU
  obtain ⟨_,_,al,_,au,_⟩ := r.verified
  have ap := (Rat.cast_pos.mpr al).trans_le ha.1
  have ab : a<1 := ha.2.trans_lt (by exact_mod_cast au)
  rw [pdf_dual_horizontal_integral_chord tp tu ap ab,
    ← horizontalPeriod_eq_jacobiChordKernel_to_seven_fifths tp tu ap ab] at bound
  have margin := positive_of_row_enclosure r bound
  push_cast at margin
  exact ⟨bound,margin⟩

theorem positive_table_branch_of_columns
    (columns : OriginalHorizontalRowsSound true (positiveData.map CheckedSignRow.toSignRow))
    (roots : ∀ r∈positiveData, ∀ t : ℝ, RealMem r.t t →
      (r.a.lower:ℝ)<verticalA t ∧ verticalA t<(r.a.upper:ℝ)) :
    ∀ r∈positiveData, ∀ t : ℝ, RealMem r.t t →
      RealMem r.hReal (actualPeriodAlong t) ∧ 3/10000<actualPeriodAlong t := by
  intro r hr t ht
  obtain ⟨al,au⟩ := roots r hr t ht
  exact positive_table_period_of_columns columns r hr t (verticalA t) ht ⟨al.le,au.le⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.positive_table_branch_of_columns

