import TwoAxisHelicoid.PdfHorizontalIntegral

namespace TwoAxisHelicoid.PdfHorizontal
open CertificateData CertificateSemantics

structure Block where
  time : Interval
  realPart : Interval
  imagPart : Interval
  abscissa : Interval

def Block.Sound (b : Block) : Prop :=
  ∀ t : ℝ, RealMem b.time t →
    RealMem b.realPart (pdfDualHorizontalIntegral t (verticalA t)).re ∧
    RealMem b.imagPart (pdfDualHorizontalIntegral t (verticalA t)).im

def Block.RectSound (b : Block) : Prop :=
  ∀ t a : ℝ, RealMem b.time t → RealMem b.abscissa a →
    RealMem b.realPart (pdfDualHorizontalIntegral t a).re ∧ RealMem b.imagPart (pdfDualHorizontalIntegral t a).im

def sourceColumn (re : Bool) (r : SignRow) : Interval := if re then r.hReal else r.hImag
def boxColumn (re : Bool) (b : Block) : Interval := if re then b.realPart else b.imagPart
noncomputable def component (re : Bool) (t : ℝ) : ℝ :=
  if re then (pdfDualHorizontalIntegral t (verticalA t)).re else (pdfDualHorizontalIntegral t (verticalA t)).im

private theorem block_component {b : Block} (sound : b.Sound) (re : Bool) {t : ℝ} (ht : RealMem b.time t) :
    RealMem (boxColumn re b) (component re t) := by
  cases re
  · exact (sound t ht).2
  · exact (sound t ht).1

/-- A rational chain can certify either component separately. The final
time is included even when it is exactly an interface of adjacent boxes. -/
def covers (re : Bool) (r : SignRow) (here : ℚ) : List Block → Bool
  | [] => false
  | b::rest =>
    if b.time.lower≤here ∧ here<b.time.upper ∧ (sourceColumn re r).lower≤(boxColumn re b).lower ∧
        (boxColumn re b).upper≤(sourceColumn re r).upper then
      decide (r.t.upper≤b.time.upper) || covers re r b.time.upper rest
    else covers re r here rest

theorem covers_value {f : ℝ → ℝ} {re : Bool} {r : SignRow} {here : ℚ} {bs : List Block}
    (each : ∀ b∈bs, ∀ x : ℝ, RealMem b.time x → RealMem (boxColumn re b) (f x)) (ok : covers re r here bs=true)
    {t : ℝ} (hl : (here:ℝ)≤t) (hu : t≤(r.t.upper:ℝ)) :
    RealMem (sourceColumn re r) (f t) := by
  induction bs generalizing here with
  | nil => simp [covers] at ok
  | cons b bs ih =>
    have tail (c : Block) (hc : c∈bs) := each c (List.mem_cons_of_mem b hc)
    simp only [covers] at ok
    split at ok
    · rename_i h
      by_cases inside : t≤(b.time.upper:ℝ)
      · have mem := each b List.mem_cons_self t
          ⟨(Rat.cast_le.mpr h.1).trans hl,inside⟩
        exact ⟨(Rat.cast_le.mpr h.2.2.1).trans mem.1,mem.2.trans (Rat.cast_le.mpr h.2.2.2)⟩
      · have fail : ¬r.t.upper≤b.time.upper := fun h => inside (hu.trans (Rat.cast_le.mpr h))
        simp only [decide_eq_false fail,Bool.false_or] at ok
        exact ih tail ok (le_of_lt (lt_of_not_ge inside))
    · exact ih tail ok hl

theorem positive_filtered_column_sound (bs : List Block) (each : ∀ b∈bs,b.Sound) (re : Bool) :
    ∀ r∈positiveData.filter (fun r => covers re r.toSignRow r.t.lower bs),
      ∀ t : ℝ, RealMem r.t t → RealMem (sourceColumn re r.toSignRow) (component re t) := by
  intro r hr t ht
  exact covers_value (fun b h _ hh => block_component (each b h) re hh) (List.mem_filter.mp hr).2 ht.1 ht.2

/-- Every accepted spatial block contains the entire original abscissa interval. -/
def matchingRectangle (r : SignRow) (b : Block) : Bool :=
  decide (b.abscissa.lower≤r.a.lower ∧ r.a.upper≤b.abscissa.upper)

theorem positive_rectangular_column_sound (bs : List Block) (each : ∀ b∈bs,b.RectSound) (re : Bool) :
    ∀ r∈positiveData.filter (fun r => covers re r.toSignRow r.t.lower (bs.filter (matchingRectangle r.toSignRow))),
      ∀ t a : ℝ, RealMem r.t t → RealMem r.a a → RealMem (sourceColumn re r.toSignRow)
        (if re then (pdfDualHorizontalIntegral t a).re else (pdfDualHorizontalIntegral t a).im) := by
  intro r hr t a ht ha
  apply covers_value (f:=fun x => if re then (pdfDualHorizontalIntegral x a).re else (pdfDualHorizontalIntegral x a).im)
    (bs:=bs.filter (matchingRectangle r.toSignRow)) _ (List.mem_filter.mp hr).2 ht.1 ht.2
  intro b hb x hx
  obtain ⟨member,matchBox⟩ := List.mem_filter.mp hb
  obtain ⟨al,au⟩ := of_decide_eq_true matchBox
  have cell := each b member x a hx ⟨(Rat.cast_le.mpr al).trans ha.1,ha.2.trans (Rat.cast_le.mpr au)⟩
  cases re
  · exact cell.2
  · exact cell.1

end TwoAxisHelicoid.PdfHorizontal
#print axioms TwoAxisHelicoid.PdfHorizontal.positive_filtered_column_sound
