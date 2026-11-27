import TwoAxisHelicoid.PdfVerticalBoxSound
import TwoAxisHelicoid.CertificateSemantics

namespace TwoAxisHelicoid.PdfVertical

theorem containedInReported_sound {u : Grid} {x : ℝ} (hx : u.Contains x)
    {lo hi : ℚ} (h : containedInReported u lo hi=true) : (lo:ℝ)≤x ∧ x≤(hi:ℝ) := by
  simp only [containedInReported,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨valid,left⟩,right⟩ := h
  obtain ⟨ul,ur⟩ := hx valid
  have left' : (lo.num:ℝ)*(Grid.denom:ℝ)≤(u.lo:ℝ)*(lo.den:ℝ) := by exact_mod_cast left
  have right' : (u.hi:ℝ)*(hi.den:ℝ)≤(hi.num:ℝ)*(Grid.denom:ℝ) := by exact_mod_cast right
  have dl : (0:ℝ)<lo.den := by exact_mod_cast lo.den_pos
  have dr : (0:ℝ)<hi.den := by exact_mod_cast hi.den_pos
  have cast_formula (q : ℚ) : (q:ℝ)=(q.num:ℝ)/(q.den:ℝ) := Rat.cast_def q
  constructor
  · rw [cast_formula,div_le_iff₀ dl]
    apply le_of_mul_le_mul_right _ Grid.real_denom_pos
    calc (lo.num:ℝ)*Grid.denom≤(u.lo:ℝ)*(lo.den:ℝ) := left'
         _ ≤ ((Grid.denom:ℝ)*x)*(lo.den:ℝ) := mul_le_mul_of_nonneg_right ul dl.le
         _ = x*(lo.den:ℝ)*Grid.denom := by ring
  · rw [cast_formula,le_div_iff₀ dr]
    apply le_of_mul_le_mul_right _ Grid.real_denom_pos
    calc x*(hi.den:ℝ)*Grid.denom=((Grid.denom:ℝ)*x)*(hi.den:ℝ) := by ring
         _ ≤ (u.hi:ℝ)*(hi.den:ℝ) := mul_le_mul_of_nonneg_right ur dr.le
         _ ≤ (hi.num:ℝ)*Grid.denom := right'

theorem verticalCover_sound {dual : Bool} {finish a lo hi here : ℚ} {cuts : List ℚ}
    (ok : verticalCover dual finish a lo hi here cuts=true) (hp : here<finish)
    {x : ℝ} (hxl : (here:ℝ)≤x) (hxu : x≤(finish:ℝ)) (hx : 0<x)
    (ha : 0<a) (hb : a<1) :
    (lo:ℝ)≤reportedVertical dual x (a:ℝ) ∧ reportedVertical dual x (a:ℝ)≤(hi:ℝ) := by
  induction cuts generalizing here with
  | nil =>
    have := of_decide_eq_true ok
    exact (hp.ne this).elim
  | cons u rest ih =>
    simp only [verticalCover,Bool.and_eq_true,decide_eq_true_eq] at ok
    by_cases hu : x≤(u:ℝ)
    · exact containedInReported_sound (verticalValueBox_contains (Grid.contains_rats hxl hu)
        (Grid.contains_rats le_rfl le_rfl) hx (by exact_mod_cast ha) (by exact_mod_cast hb) dual) ok.1.2
    · have hlt := lt_of_not_ge hu
      have huf : u<finish := by exact_mod_cast hlt.trans_le hxu
      exact ih ok.2 huf hlt.le

/-- The eight rational endpoints copied from the two columns and their
input rectangle. Mesh cut points play no part in their identity. -/
structure VerticalKey where
  tLo : ℚ
  tHi : ℚ
  aLo : ℚ
  aHi : ℚ
  low : CertificateData.Interval
  high : CertificateData.Interval

def VerticalRow.key (r : VerticalRow) : VerticalKey :=
  ⟨r.tLo,r.tHi,r.aLo,r.aHi,⟨r.vLoLeft,r.vLoRight⟩,⟨r.vHiLeft,r.vHiRight⟩⟩

def originalKey (r : CertificateData.SignRow) : VerticalKey :=
  ⟨r.t.lower,r.t.upper,r.a.lower,r.a.upper,r.verticalLower,r.verticalUpper⟩

def VerticalKey.Sound (r : VerticalKey) : Prop :=
  ∀ x : ℝ, (r.tLo:ℝ)≤x → x≤(r.tHi:ℝ) →
    CertificateSemantics.RealMem r.low (reportedVertical (decide (r.tHi<3/5)) x r.aLo) ∧
    CertificateSemantics.RealMem r.high (reportedVertical (decide (r.tHi<3/5)) x r.aHi)

theorem VerticalRow.sound {r : VerticalRow} (h : r.verified=true) : r.key.Sound := by
  simp only [VerticalRow.verified,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨ht,hT,ha,hab,hb⟩,left⟩,right⟩ := h
  intro x hl hu
  have hx : 0<x := (Rat.cast_pos.mpr ht).trans_le hl
  exact ⟨verticalCover_sound left hT hl hu hx ha (hab.trans hb),
    verticalCover_sound right hT hl hu hx (ha.trans hab) hb⟩

/-- Transfer soundness by equality of the entire vector of original
endpoints. This identifies the reported intervals as well as the inputs. -/
theorem transfer_vertical_rows {b : Bool} {m : ℚ} {rows : List (CertificateData.CheckedSignRow b m)}
    {checked : List VerticalRow} (valid : checked.all VerticalRow.verified=true)
    (same : checked.map VerticalRow.key=rows.map (fun r => originalKey r.toSignRow)) :
    ∀ r∈rows, (originalKey r.toSignRow).Sound := by
  intro r hr
  have mem : originalKey r.toSignRow ∈ rows.map (fun s => originalKey s.toSignRow) :=
    List.mem_map.mpr ⟨r,hr,rfl⟩
  rw [← same] at mem
  obtain ⟨s,hs,e⟩ := List.mem_map.mp mem
  rw [← e]
  exact VerticalRow.sound (List.all_eq_true.mp valid s hs)

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.transfer_vertical_rows
