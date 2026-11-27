import TwoAxisHelicoid.PdfComplexChordKernel

namespace TwoAxisHelicoid.PdfVertical
open Complex Metric Set

/-- A bound on a rectangular region includes holomorphy at each of its points. -/
def ChordRectangleBound (xl xu yl yu M : ℚ) (t a : ℝ) : Prop :=
  ∀ z : ℂ, z.re∈Icc (xl:ℝ) (xu:ℝ) → z.im∈Icc (yl:ℝ) (yu:ℝ) →
    ‖jacobiChordKernel t a z‖≤(M:ℝ) ∧ DifferentiableAt ℂ (jacobiChordKernel t a) z

def chordRectangleTest (terms : ℕ) (par : ChordParams) (xl xu yl yu M : ℚ) : Bool :=
  let f := complexChordFrame par (Grid.ofRats xl xu) (Grid.ofRats yl yu)
  let b := complexChordValue terms par f
  f.regular par && b.ok && decide ((b.mag:ℚ)≤M*(Grid.denom:ℚ))

theorem chordRectangleTest_sound {terms : ℕ} {p : ChordParams} {xl xu yl yu M : ℚ}
    {t a : ℝ} (ps : p.Sound t a) (ht : 0<t) (valid : chordRectangleTest terms p xl xu yl yu M=true) :
    ChordRectangleBound xl xu yl yu M t a := by
  let f := complexChordFrame p (Grid.ofRats xl xu) (Grid.ofRats yl yu)
  let b := complexChordValue terms p f
  change ((f.regular p && b.ok) && decide ((b.mag:ℚ)≤M*(Grid.denom:ℚ)))=true at valid
  obtain ⟨⟨regular,ok⟩,m⟩ := (Bool.and_eq_true_iff.mp valid).imp Bool.and_eq_true_iff.mp of_decide_eq_true
  intro z x y
  have fr := complexChordFrame_sound ps (Grid.contains_rats x.1 x.2) (Grid.contains_rats y.1 y.2)
  obtain ⟨out,derivative⟩ := complexChordValue_sound terms ps fr ht regular
  refine ⟨(CGrid.norm_le_mag out ok).trans ?_,derivative⟩
  rw [Grid.value,div_le_iff₀ Grid.real_denom_pos]
  have h := (Rat.cast_le (K:=ℝ)).mpr m
  push_cast at h
  exact h

theorem ChordRectangleBound.joinX {l m u yl yu M : ℚ} {t a : ℝ}
    (left : ChordRectangleBound l m yl yu M t a) (right : ChordRectangleBound m u yl yu M t a) :
    ChordRectangleBound l u yl yu M t a := by
  intro z hx hy
  by_cases h : z.re≤(m:ℝ)
  · exact left z ⟨hx.1,h⟩ hy
  · exact right z ⟨le_of_lt (lt_of_not_ge h),hx.2⟩ hy

theorem ChordRectangleBound.joinY {xl xu l m u M : ℚ} {t a : ℝ}
    (lower : ChordRectangleBound xl xu l m M t a) (upper : ChordRectangleBound xl xu m u M t a) :
    ChordRectangleBound xl xu l u M t a := by
  intro z hx hy
  by_cases h : z.im≤(m:ℝ)
  · exact lower z hx ⟨hy.1,h⟩
  · exact upper z hx ⟨le_of_lt (lt_of_not_ge h),hy.2⟩

def ChordDiskBound (c R M : ℚ) (t a : ℝ) : Prop :=
  ∀ z ∈ closedBall (c:ℂ) (R:ℝ),
    ‖jacobiChordKernel t a z‖≤(M:ℝ) ∧ DifferentiableAt ℂ (jacobiChordKernel t a) z

theorem chordDiskBound_of_square {c R M : ℚ} {t a : ℝ}
    (square : ChordRectangleBound (c-R) (c+R) (-R) R M t a) : ChordDiskBound c R M t a := by
  intro z hz
  have small := mem_closedBall_iff_norm.mp hz
  have re := abs_le.mp ((Complex.abs_re_le_norm _).trans small)
  have im := abs_le.mp ((Complex.abs_im_le_norm _).trans small)
  have center : (c:ℂ)=((c:ℝ):ℂ) := (Complex.ofReal_ratCast c).symm
  rw [center,Complex.sub_re,Complex.ofReal_re] at re
  rw [center,Complex.sub_im,Complex.ofReal_im,sub_zero] at im
  apply square
  · simp only [mem_Icc,Rat.cast_sub,Rat.cast_add]
    constructor <;> linarith [re.1,re.2]
  · simpa only [mem_Icc,Rat.cast_neg] using im

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.chordDiskBound_of_square
#print axioms TwoAxisHelicoid.PdfVertical.chordRectangleTest_sound

