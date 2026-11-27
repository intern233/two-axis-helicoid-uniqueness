import TwoAxisHelicoid.PdfVerticalKeyEquality
import TwoAxisHelicoid.PdfEndpointVerticalCut
import TwoAxisHelicoid.PdfDerivativeVerticalRows000
import TwoAxisHelicoid.PdfDerivativeVerticalRows010
import TwoAxisHelicoid.PdfDerivativeVerticalRows020
import TwoAxisHelicoid.PdfDerivativeVerticalRows030
import TwoAxisHelicoid.PdfDerivativeVerticalRows040

namespace TwoAxisHelicoid.PdfVertical
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open CertificateData CertificateSemantics
def derivativeVerticalKey (r : CheckedDerivativeRow) : VerticalKey :=
  ⟨r.t.lower,r.t.upper,r.a.lower,r.a.upper,⟨r.verticalLower,100⟩,⟨-100,r.verticalUpper⟩⟩

def derivativeVerticalRows := derivativeVerticalRows000 ++ derivativeVerticalRows010 ++ derivativeVerticalRows020 ++ derivativeVerticalRows030 ++ derivativeVerticalRows040

theorem derivative_table_actual_vertical_bounds :
    ∀ r∈derivativeData, ∀ t : ℝ, RealMem r.t t →
      (r.verticalLower:ℝ)≤(thetaG t (r.a.lower:ℝ)).re ∧
      (thetaG t (r.a.upper:ℝ)).re≤(r.verticalUpper:ℝ) := by
  have valid : derivativeVerticalRows.all VerticalRow.verified=true := by
    simp only [derivativeVerticalRows,List.all_append,derivativeVerticalRows000_checked,derivativeVerticalRows010_checked,derivativeVerticalRows020_checked,derivativeVerticalRows030_checked,derivativeVerticalRows040_checked,Bool.and_self]
  have matchRows : derivativeVerticalRows.map VerticalRow.key=derivativeData.map derivativeVerticalKey := by decide +kernel
  have unscaled : derivativeData.all (fun r => decide (3/5≤r.t.upper))=true := by decide +kernel
  intro r member t ht
  have membership : derivativeVerticalKey r∈derivativeData.map derivativeVerticalKey :=
    List.mem_map.mpr ⟨r,member,rfl⟩
  rw [← matchRows] at membership
  obtain ⟨s,hs,eqn⟩ := List.mem_map.mp membership
  have h := VerticalRow.sound (List.all_eq_true.mp valid s hs)
  change s.key.Sound at h
  rw [eqn] at h
  obtain ⟨lower,upper⟩ := h t ht.1 ht.2
  have flag : ¬r.t.upper<3/5 := not_lt.mpr (of_decide_eq_true (List.all_eq_true.mp unscaled r member))
  have combined := And.intro lower.1 upper.2
  change (r.verticalLower:ℝ)≤reportedVertical (decide (r.t.upper<3/5)) t r.a.lower ∧
    reportedVertical (decide (r.t.upper<3/5)) t r.a.upper≤(r.verticalUpper:ℝ) at combined
  rw [show decide (r.t.upper<(3/5:ℚ))=false from decide_eq_false flag] at combined
  exact combined

theorem endpoint_table_actual_vertical_lower {t : ℝ} (hl : 7/5≤t) (hu : t≤141/100) :
    (63756382130020915978949311/1237940039285380274899124224:ℝ)≤(thetaG t (9/10)).re := by
  have h := verticalCover_sound rightEndpointLowerCut (by norm_num)
    (x:=t) (by simpa only [Rat.cast_div,Rat.cast_ofNat] using hl)
    (by simpa only [Rat.cast_div,Rat.cast_ofNat] using hu) (lt_of_lt_of_le (by norm_num) hl)
    (by norm_num) (by norm_num)
  simpa only [reportedVertical,Bool.false_eq_true,ite_false,Rat.cast_div,Rat.cast_ofNat] using h.1

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.derivative_table_actual_vertical_bounds
#print axioms TwoAxisHelicoid.PdfVertical.endpoint_table_actual_vertical_lower
