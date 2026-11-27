import TwoAxisHelicoid.PdfChordRectangleSound

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics

/-- A checked rectangle contains a range of original parameter boxes and
its complex output lies inside both source columns of each such box. -/
def HorizontalRectangle.coversRow (b : HorizontalRectangle) (dual : Bool) (s : SignRow) : Bool :=
  decide (b.isDual=dual ∧ b.tLo≤s.t.lower ∧ s.t.upper≤b.tHi ∧ b.aLo≤s.a.lower ∧ s.a.upper≤b.aHi ∧
    s.hReal.lower≤b.reLo ∧ b.reHi≤s.hReal.upper ∧ s.hImag.lower≤b.imLo ∧ b.imHi≤s.hImag.upper)

def HorizontalRectangle.Sound (b : HorizontalRectangle) : Prop :=
  ∀ t a : ℝ, (b.tLo:ℝ)≤t → t≤(b.tHi:ℝ) → (b.aLo:ℝ)≤a → a≤(b.aHi:ℝ) →
    b.Encloses (sourceHorizontalIntegral b.isDual t a)

theorem HorizontalRectangle.sound_of_check (b : HorizontalRectangle) {n m : ℕ}
    (ok : horizontalRectanglePieces b n m b.tLo b.tHi b.aLo b.aHi=true) : b.Sound := by
  intro t a ht hu ha hb
  exact horizontalRectanglePieces_sound b n m _ _ _ _ ok ht hu ha hb

theorem HorizontalRectangle.row_sound {b : HorizontalRectangle} {dual : Bool} {s : SignRow}
    (cert : b.Sound) (matchBox : b.coversRow dual s=true)
    {t a : ℝ} (ht : RealMem s.t t) (ha : RealMem s.a a) :
    RealMem s.hReal (sourceHorizontalIntegral dual t a).re ∧
    RealMem s.hImag (sourceHorizontalIntegral dual t a).im := by
  obtain ⟨mode,tl,tu,al,au,rl,ru,il,iu⟩ := of_decide_eq_true matchBox
  obtain ⟨rlo,rhi,ilo,ihi⟩ := cert t a ((Rat.cast_le.mpr tl).trans ht.1) (ht.2.trans (Rat.cast_le.mpr tu))
    ((Rat.cast_le.mpr al).trans ha.1) (ha.2.trans (Rat.cast_le.mpr au))
  rw [← mode]
  exact ⟨⟨(Rat.cast_le.mpr rl).trans rlo,rhi.trans (Rat.cast_le.mpr ru)⟩,
    ⟨(Rat.cast_le.mpr il).trans ilo,ihi.trans (Rat.cast_le.mpr iu)⟩⟩

theorem actual_rows_covered_by_rectangles (boxes : List HorizontalRectangle)
    (cert : ∀ b∈boxes, b.Sound) {dual : Bool} {s : SignRow}
    (cover : boxes.any (fun b => b.coversRow dual s)=true)
    {t a : ℝ} (ht : RealMem s.t t) (ha : RealMem s.a a) :
    RealMem s.hReal (sourceHorizontalIntegral dual t a).re ∧
    RealMem s.hImag (sourceHorizontalIntegral dual t a).im := by
  obtain ⟨b,hb,inside⟩ := List.any_eq_true.mp cover
  exact HorizontalRectangle.row_sound (cert b hb) inside ht ha

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.actual_rows_covered_by_rectangles
