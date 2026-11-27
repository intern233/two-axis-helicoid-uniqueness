import TwoAxisHelicoid.PdfChordIntegralSound

namespace TwoAxisHelicoid.PdfVertical

/-- The source stores the half-period of the dual path on the positive
side and one half of the full primal period on the negative side. -/
noncomputable def sourceHorizontalIntegral (dual : Bool) (t a : ℝ) : ℂ :=
  if dual then pdfDualHorizontalIntegral t a else pdfPrimalHorizontalIntegral t a

def HorizontalRectangle.Encloses (r : HorizontalRectangle) (z : ℂ) : Prop :=
  (r.reLo:ℝ)≤z.re ∧ z.re≤(r.reHi:ℝ) ∧ (r.imLo:ℝ)≤z.im ∧ z.im≤(r.imHi:ℝ)

theorem horizontalRectangleCheck_sound {r : HorizontalRectangle} {tl tu al au : ℚ}
    (valid : horizontalRectangleCheck r tl tu al au=true)
    {t a : ℝ} (tlb : (tl:ℝ)≤t) (tub : t≤(tu:ℝ)) (alb : (al:ℝ)≤a) (aub : a≤(au:ℝ)) :
    r.Encloses (sourceHorizontalIntegral r.isDual t a) := by
  simp only [horizontalRectangleCheck,Bool.and_eq_true,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨htl,_,htu,hal,_,hau⟩,hre⟩,him⟩ := valid
  have ht := (Rat.cast_pos.mpr htl).trans_le tlb
  have hu : t≤7/5 := tub.trans (by
    simpa only [Rat.cast_div,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr htu)
  have ha := (Rat.cast_pos.mpr hal).trans_le alb
  have hb : a<1 := aub.trans_lt (by exact_mod_cast hau)
  have p := chordParams_sound (Grid.contains_rats tlb tub) (Grid.contains_rats alb aub) ht
  have out := chordTiles_sound p ht hu 1 (-1) r.tiles
  simp only [Rat.cast_neg,Rat.cast_one] at out
  have realPart := containedInReported_sound out.1 hre
  cases mode : r.isDual with
  | false =>
    simp only [mode,Bool.false_eq_true,ite_false,decide_eq_true_eq] at him
    unfold HorizontalRectangle.Encloses sourceHorizontalIntegral
    simp only [Bool.false_eq_true,ite_false]
    rw [pdf_primal_horizontal_integral_real ht,Complex.ofReal_re,Complex.ofReal_im,
      horizontalPeriod_eq_jacobiChordKernel_to_seven_fifths ht hu ha hb]
    exact ⟨realPart.1,realPart.2,by exact_mod_cast him.1,by exact_mod_cast him.2⟩
  | true =>
    simp only [mode,ite_true] at him
    have imagPart := containedInReported_sound out.2 him
    unfold HorizontalRectangle.Encloses sourceHorizontalIntegral
    simp only [ite_true]
    rw [pdf_dual_horizontal_integral_chord ht hu ha hb]
    exact ⟨realPart.1,realPart.2,imagPart.1,imagPart.2⟩

/-- Bisection covers both closed coordinates. The interval on every leaf
must certify the same original pair of output columns. -/
theorem horizontalRectanglePieces_sound (r : HorizontalRectangle) (n m : ℕ)
    (tl tu al au : ℚ) (valid : horizontalRectanglePieces r n m tl tu al au=true)
    {t a : ℝ} (tlb : (tl:ℝ)≤t) (tub : t≤(tu:ℝ)) (alb : (al:ℝ)≤a) (aub : a≤(au:ℝ)) :
    r.Encloses (sourceHorizontalIntegral r.isDual t a) := by
  induction n generalizing tl tu with
  | zero =>
    induction m generalizing al au with
    | zero => exact horizontalRectangleCheck_sound valid tlb tub alb aub
    | succ m ih =>
      simp only [horizontalRectanglePieces,horizontalRectangleAPieces,Bool.and_eq_true] at valid
      obtain ⟨left,right⟩ := valid
      by_cases h : a≤(((al+au)/2:ℚ):ℝ)
      · apply ih al ((al+au)/2) <;> assumption
      · have hm : (((al+au)/2:ℚ):ℝ)≤a := le_of_lt (lt_of_not_ge h)
        apply ih ((al+au)/2) au <;> assumption
  | succ n ih =>
    simp only [horizontalRectanglePieces,Bool.and_eq_true] at valid
    obtain ⟨left,right⟩ := valid
    by_cases h : t≤(((tl+tu)/2:ℚ):ℝ)
    · exact ih tl ((tl+tu)/2) left tlb h
    · exact ih ((tl+tu)/2) tu right (le_of_lt (lt_of_not_ge h)) tub

def HorizontalRectangle.Matches (r : HorizontalRectangle) (dual : Bool) (s : CertificateData.SignRow) : Prop :=
  r.isDual=dual ∧ r.tLo=s.t.lower ∧ r.tHi=s.t.upper ∧ r.aLo=s.a.lower ∧ r.aHi=s.a.upper ∧
    r.reLo=s.hReal.lower ∧ r.reHi=s.hReal.upper ∧ r.imLo=s.hImag.lower ∧ r.imHi=s.hImag.upper
  deriving Decidable

theorem horizontal_original_row {r : HorizontalRectangle} {dual : Bool} {s : CertificateData.SignRow}
    (hm : r.Matches dual s) {n m : ℕ}
    (ok : horizontalRectanglePieces r n m r.tLo r.tHi r.aLo r.aHi=true) :
    ∀ t a : ℝ, CertificateSemantics.RealMem s.t t → CertificateSemantics.RealMem s.a a →
      CertificateSemantics.RealMem s.hReal (sourceHorizontalIntegral dual t a).re ∧
      CertificateSemantics.RealMem s.hImag (sourceHorizontalIntegral dual t a).im := by
  obtain ⟨mode,t0,t1,a0,a1,r0,r1,i0,i1⟩ := hm
  intro t a ht ha
  have h := horizontalRectanglePieces_sound _ _ _ _ _ _ _ ok
    (t0.symm ▸ ht.1) (t1.symm ▸ ht.2) (a0.symm ▸ ha.1) (a1.symm ▸ ha.2)
  unfold HorizontalRectangle.Encloses at h
  rw [mode,r0,r1,i0,i1] at h
  exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.horizontal_original_row
