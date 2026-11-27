import TwoAxisHelicoid.ComplexBall

/-! Outward dyadic rounding, proved using exact rational floor and ceiling. -/

namespace TwoAxisHelicoid
namespace ComplexBall

def roundingStep (prec : ℕ) : ℚ := 1/(2^prec : ℚ)
def roundDown (prec : ℕ) (q : ℚ) : ℚ := (⌊q*(2^prec : ℚ)⌋ : ℚ)/(2^prec : ℚ)
def roundUp (prec : ℕ) (q : ℚ) : ℚ := (⌈q*(2^prec : ℚ)⌉ : ℚ)/(2^prec : ℚ)

theorem roundDown_le (prec : ℕ) (q : ℚ) : roundDown prec q ≤ q := by
  unfold roundDown
  exact (div_le_iff₀ (by positivity)).mpr (Int.floor_le _)

theorem lt_roundDown_add (prec : ℕ) (q : ℚ) : q < roundDown prec q + roundingStep prec := by
  unfold roundDown roundingStep
  rw [← add_div]
  exact (lt_div_iff₀ (by positivity)).mpr (Int.lt_floor_add_one _)

theorem le_roundUp (prec : ℕ) (q : ℚ) : q ≤ roundUp prec q := by
  unfold roundUp
  exact (le_div_iff₀ (by positivity)).mpr (Int.le_ceil _)

theorem roundDown_error (prec : ℕ) (q : ℚ) : |q-roundDown prec q| ≤ roundingStep prec := by
  rw [abs_of_nonneg (sub_nonneg.mpr (roundDown_le prec q))]
  linarith [lt_roundDown_add prec q]

def round (prec : ℕ) (b : ComplexBall) : ComplexBall :=
  ⟨⟨roundDown prec b.center.re, roundDown prec b.center.im⟩,
    roundUp prec (b.radius+2*roundingStep prec)⟩

theorem round_coarsens (prec : ℕ) (b : ComplexBall) : (round prec b).coarsens b := by
  have hr := roundDown_error prec b.center.re
  have hi := roundDown_error prec b.center.im
  have hu := le_roundUp prec (b.radius+2*roundingStep prec)
  unfold coarsens round QComplex.absUpper QComplex.sub QComplex.add QComplex.neg
  dsimp
  simpa only [sub_eq_add_neg] using (show
    |b.center.re-roundDown prec b.center.re|+|b.center.im-roundDown prec b.center.im|+b.radius ≤
      roundUp prec (b.radius+2*roundingStep prec) by linarith)

theorem round_contains {b : ComplexBall} {z : ℂ} (hb : b.Contains z) (prec : ℕ) :
    (round prec b).Contains z := coarsen_contains hb (round_coarsens prec b)

def roundedAdd (prec : ℕ) (a b : ComplexBall) : ComplexBall := round prec (add a b)
def roundedMul (prec : ℕ) (a b : ComplexBall) : ComplexBall := round prec (mul a b)
def roundedInv (prec : ℕ) (a : ComplexBall) : ComplexBall := round prec (inv a)

theorem roundedAdd_contains {a b : ComplexBall} {z w : ℂ}
    (ha : a.Contains z) (hb : b.Contains w) (prec : ℕ) :
    (roundedAdd prec a b).Contains (z+w) := round_contains (add_contains ha hb) prec

theorem roundedMul_contains {a b : ComplexBall} {z w : ℂ}
    (ha : a.Contains z) (hb : b.Contains w) (prec : ℕ) :
    (roundedMul prec a b).Contains (z*w) := round_contains (mul_contains ha hb) prec

theorem roundedInv_contains {a : ComplexBall} {z : ℂ} (ha : a.Contains z)
    (hl : 0 < a.lower) (prec : ℕ) :
    (roundedInv prec a).Contains z⁻¹ := round_contains (inv_contains ha hl) prec

end ComplexBall
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ComplexBall.round_contains
