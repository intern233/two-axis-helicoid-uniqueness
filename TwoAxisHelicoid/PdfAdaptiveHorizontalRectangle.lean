import TwoAxisHelicoid.PdfAdaptiveChordIntegral
import TwoAxisHelicoid.PdfHorizontalGroupedTransfer

namespace TwoAxisHelicoid.PdfVertical

/-- Conversion from a checked full contour to the two columns printed by the
source. On the full-period path the imaginary coordinate vanishes identically. -/
theorem adaptive_horizontal_encloses {b : HorizontalRectangle} {p : ChordParams}
    {t a : ℝ} (data : p.Sound t a) (ht : 0<t) (hu : t≤7/5) (ha : 0<a) (hb : a<1)
    (path : AdaptiveChordPath) {N : ℕ} (valid : path.checked N p=true)
    (ends : path.lower= -1 ∧ path.upper=1)
    (inside : containedInReported path.output.re b.reLo b.reHi=true ∧
      (if b.isDual then containedInReported path.output.im b.imLo b.imHi else
        decide (b.imLo≤0 ∧ 0≤b.imHi))=true) :
    b.Encloses (sourceHorizontalIntegral b.isDual t a) := by
  have val := path.integral data ht hu valid
  rw [ends.1,ends.2] at val
  simp only [Rat.cast_neg,Rat.cast_one] at val
  obtain ⟨re,im⟩ := inside
  have r := containedInReported_sound val.1 re
  cases mode : b.isDual with
  | false =>
    simp only [mode,Bool.false_eq_true,ite_false,decide_eq_true_eq] at im
    unfold HorizontalRectangle.Encloses sourceHorizontalIntegral
    simp only [Bool.false_eq_true,ite_false]
    rw [pdf_primal_horizontal_integral_real ht,Complex.ofReal_re,Complex.ofReal_im,
      horizontalPeriod_eq_jacobiChordKernel_to_seven_fifths ht hu ha hb]
    exact ⟨r.1,r.2,by exact_mod_cast im.1,by exact_mod_cast im.2⟩
  | true =>
    simp only [mode,ite_true] at im
    have i := containedInReported_sound val.2 im
    unfold HorizontalRectangle.Encloses sourceHorizontalIntegral
    simp only [ite_true]
    rw [pdf_dual_horizontal_integral_chord ht hu ha hb]
    exact ⟨r.1,r.2,i.1,i.2⟩

theorem adaptive_horizontal_on_box {b : HorizontalRectangle} {p : ChordParams} {tl tu al au : ℚ}
    (par : chordParams (Grid.ofRats tl tu) (Grid.ofRats al au)=p)
    (domain : 0<tl ∧ tu≤7/5 ∧ 0<al ∧ au<1)
    (path : AdaptiveChordPath) {N : ℕ} (ok : path.checked N p=true)
    (ends : path.lower= -1 ∧ path.upper=1)
    (inside : containedInReported path.output.re b.reLo b.reHi=true ∧
      (if b.isDual then containedInReported path.output.im b.imLo b.imHi else
        decide (b.imLo≤0 ∧ 0≤b.imHi))=true)
    {t a : ℝ} (lt : (tl:ℝ)≤t) (ut : t≤(tu:ℝ)) (la : (al:ℝ)≤a) (ua : a≤(au:ℝ)) :
    b.Encloses (sourceHorizontalIntegral b.isDual t a) := by
  obtain ⟨pT,uT,pA,uA⟩ := domain
  have ht := (Rat.cast_pos.mpr pT).trans_le lt
  have hu : t≤7/5 := ut.trans (by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr uT)
  have ha := (Rat.cast_pos.mpr pA).trans_le la
  have hb : a<1 := ua.trans_lt (by exact_mod_cast uA)
  have ps := chordParams_sound (Grid.contains_rats lt ut) (Grid.contains_rats la ua) ht
  rw [par] at ps
  exact adaptive_horizontal_encloses ps ht hu ha hb path ok ends inside

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.adaptive_horizontal_on_box
