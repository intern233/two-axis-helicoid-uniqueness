import TwoAxisHelicoid.ComplexBallExp

/-! Checked operations reject uncertified division or exponential truncation. -/

namespace TwoAxisHelicoid
namespace ComplexBall

def Sound (b : Option ComplexBall) (z : ℂ) : Prop := ∀ out, b = some out → out.Contains z

theorem sound_some {b : ComplexBall} {z : ℂ} (hb : b.Contains z) : Sound (some b) z := by
  intro out hout
  cases Option.some.inj hout
  exact hb

def mapTwo (f : ComplexBall → ComplexBall → ComplexBall)
    (a b : Option ComplexBall) : Option ComplexBall := do
  let aa ← a
  let bb ← b
  pure (f aa bb)

theorem mapTwo_sound {a b : Option ComplexBall} {z w u : ℂ}
    (ha : Sound a z) (hb : Sound b w) (f : ComplexBall → ComplexBall → ComplexBall)
    (hf : ∀ aa bb, aa.Contains z → bb.Contains w → (f aa bb).Contains u) :
    Sound (mapTwo f a b) u := by
  cases a with
  | none => simp [Sound, mapTwo]
  | some aa =>
    cases b with
    | none => simp [Sound, mapTwo]
    | some bb =>
      exact sound_some (hf aa bb (ha aa rfl) (hb bb rfl))

def checkedInv (prec : ℕ) (b : ComplexBall) : Option ComplexBall :=
  if 0 < b.lower then some (roundedInv prec b) else none

theorem checkedInv_sound {b : ComplexBall} {z : ℂ} (hb : b.Contains z) (prec : ℕ) :
    Sound (checkedInv prec b) z⁻¹ := by
  unfold checkedInv
  split_ifs with h
  · exact sound_some (roundedInv_contains hb h prec)
  · simp [Sound]

def checkedExp (prec n s : ℕ) (b : ComplexBall) : Option ComplexBall :=
  if expGuard (scale (1/(2^s : ℚ)) b) n then some (expScaled prec n s b) else none

theorem checkedExp_sound {b : ComplexBall} {z : ℂ} (hb : b.Contains z) (prec n s : ℕ) :
    Sound (checkedExp prec n s b) (Complex.exp z) := by
  unfold checkedExp
  split_ifs with h
  · exact sound_some (expScaled_contains hb prec n s h)
  · simp [Sound]

def realInterval (lo hi : ℚ) : ComplexBall :=
  ⟨QComplex.ofRat ((lo+hi)/2), (hi-lo)/2⟩

theorem realInterval_contains {lo hi : ℚ} {x : ℝ} (hl : (lo : ℝ) ≤ x) (hu : x ≤ (hi : ℝ)) :
    (realInterval lo hi).Contains (x : ℂ) := by
  simp only [Contains, realInterval, QComplex.val_ofRat]
  rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  push_cast
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def piBall : ComplexBall :=
  realInterval (314159265358979323846/10^20) (314159265358979323847/10^20)

theorem piBall_contains : piBall.Contains (Real.pi : ℂ) := by
  apply realInterval_contains
  · have h := Real.pi_gt_d20.le
    norm_num at h ⊢
    exact h
  · have h := Real.pi_lt_d20.le
    norm_num at h ⊢
    exact h

theorem re_bounds {b : ComplexBall} {z : ℂ} (hb : b.Contains z) :
    (b.center.re-b.radius : ℚ) ≤ z.re ∧ z.re ≤ (b.center.re+b.radius : ℚ) := by
  have h := (Complex.abs_re_le_norm (z-b.center.val)).trans hb
  have ha := abs_le.mp h
  simp only [Complex.sub_re, QComplex.val] at ha
  push_cast
  constructor <;> linarith [ha.1, ha.2]

theorem abs_im_le {b : ComplexBall} {z : ℂ} (hb : b.Contains z) :
    |z.im| ≤ (|b.center.im|+b.radius : ℚ) := by
  have h := (Complex.abs_im_le_norm (z-b.center.val)).trans hb
  simp only [Complex.sub_im, QComplex.val] at h
  have ha := abs_add_le (z.im-(b.center.im : ℝ)) (b.center.im : ℝ)
  rw [sub_add_cancel] at ha
  push_cast
  linarith

end ComplexBall
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ComplexBall.checkedExp_sound
#print axioms TwoAxisHelicoid.ComplexBall.piBall_contains
