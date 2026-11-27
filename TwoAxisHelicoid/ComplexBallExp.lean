import TwoAxisHelicoid.ComplexBallRound

/-! A kernel-checkable exponential enclosure with Taylor remainder and repeated squaring. -/

namespace TwoAxisHelicoid
namespace ComplexBall

def rational (q : ℚ) : ComplexBall := point (QComplex.ofRat q)

theorem rational_contains (q : ℚ) : (rational q).Contains (q : ℂ) := by
  simpa only [rational, QComplex.val_ofRat] using point_contains (QComplex.ofRat q)

def scale (q : ℚ) (b : ComplexBall) : ComplexBall := mul (rational q) b

theorem scale_contains {b : ComplexBall} {z : ℂ} (hb : b.Contains z) (q : ℚ) :
    (scale q b).Contains ((q : ℂ)*z) := mul_contains (rational_contains q) hb

/-- The partial sum through n-1 and the next Taylor term, all rounded outward. -/
def expSumAndTerm (prec : ℕ) (b : ComplexBall) : ℕ → ComplexBall × ComplexBall
  | 0 => (rational 0, rational 1)
  | n+1 =>
    let p := expSumAndTerm prec b n
    (roundedAdd prec p.1 p.2,
      roundedMul prec (roundedMul prec p.2 b) (rational (1/(n+1 : ℚ))))

theorem expSumAndTerm_contains {b : ComplexBall} {z : ℂ} (hb : b.Contains z) (prec n : ℕ) :
    (expSumAndTerm prec b n).1.Contains (∑ k ∈ Finset.range n, z^k/(k.factorial : ℂ)) ∧
    (expSumAndTerm prec b n).2.Contains (z^n/(n.factorial : ℂ)) := by
  induction n with
  | zero =>
    constructor
    · simpa [expSumAndTerm] using rational_contains 0
    · simpa [expSumAndTerm] using rational_contains 1
  | succ n ih =>
    constructor
    · simpa only [expSumAndTerm, Finset.sum_range_succ] using roundedAdd_contains ih.1 ih.2 prec
    · have h := roundedMul_contains (roundedMul_contains ih.2 hb prec)
        (rational_contains (1/(n+1 : ℚ))) prec
      convert h using 1
      · rfl
      · push_cast
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp

def expError (b : ComplexBall) (n : ℕ) : ℚ :=
  (b.center.absUpper+b.radius)^n/(n.factorial : ℚ)*2

def expGuard (b : ComplexBall) (n : ℕ) : Prop :=
  (b.center.absUpper+b.radius)/(n+1 : ℚ) ≤ 1/2

instance (b : ComplexBall) (n : ℕ) : Decidable (expGuard b n) := inferInstanceAs
  (Decidable ((b.center.absUpper+b.radius)/(n+1 : ℚ) ≤ 1/2))

def expTaylor (prec n : ℕ) (b : ComplexBall) : ComplexBall :=
  let p := (expSumAndTerm prec b n).1
  round prec ⟨p.center, p.radius+expError b n⟩

theorem expTaylor_contains {b : ComplexBall} {z : ℂ} (hb : b.Contains z)
    (prec n : ℕ) (hg : expGuard b n) : (expTaylor prec n b).Contains (Complex.exp z) := by
  have hnorm := norm_le hb
  have hm : (0 : ℝ) ≤ (b.center.absUpper+b.radius : ℚ) := (norm_nonneg z).trans hnorm
  have hguard : ‖z‖/(n+1 : ℝ) ≤ 1/2 := by
    have hgrat : ((b.center.absUpper+b.radius : ℚ) : ℝ)/(n+1 : ℝ) ≤ 1/2 := by
      unfold expGuard at hg
      have hh : (((b.center.absUpper+b.radius)/(n+1 : ℚ) : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ) :=
        Rat.cast_le.mpr hg
      simpa using hh
    exact (div_le_div_of_nonneg_right hnorm (by positivity)).trans hgrat
  have herr := Complex.exp_bound' (x := z) (n := n)
    (by simpa only [Nat.cast_succ] using hguard)
  have herr' : ‖Complex.exp z - ∑ k ∈ Finset.range n, z^k/(k.factorial : ℂ)‖ ≤
      (expError b n : ℝ) := by
    apply herr.trans
    unfold expError
    push_cast
    gcongr
    simpa only [Rat.cast_add] using hnorm
  have hp := (expSumAndTerm_contains hb prec n).1
  unfold expTaylor
  apply round_contains
  unfold Contains at *
  dsimp
  push_cast
  have hn := norm_add_le
    (Complex.exp z - ∑ k ∈ Finset.range n, z^k/(k.factorial : ℂ))
    ((∑ k ∈ Finset.range n, z^k/(k.factorial : ℂ)) - (expSumAndTerm prec b n).1.center.val)
  rw [sub_add_sub_cancel] at hn
  linarith

/-- s squarings implement the power 2^s with linear complexity in s. -/
def repeatedSquare (prec : ℕ) (b : ComplexBall) : ℕ → ComplexBall
  | 0 => b
  | s+1 => let c := repeatedSquare prec b s; roundedMul prec c c

theorem repeatedSquare_contains {b : ComplexBall} {z : ℂ} (hb : b.Contains z) (prec s : ℕ) :
    (repeatedSquare prec b s).Contains (z^(2^s)) := by
  induction s with
  | zero => simpa [repeatedSquare] using hb
  | succ s ih =>
    simpa only [repeatedSquare, pow_succ, ← pow_add, ← two_mul,
      Nat.mul_comm 2 (2^s)] using roundedMul_contains ih ih prec

def expScaled (prec n s : ℕ) (b : ComplexBall) : ComplexBall :=
  repeatedSquare prec (expTaylor prec n (scale (1/(2^s : ℚ)) b)) s

theorem expScaled_contains {b : ComplexBall} {z : ℂ} (hb : b.Contains z)
    (prec n s : ℕ) (hg : expGuard (scale (1/(2^s : ℚ)) b) n) :
    (expScaled prec n s b).Contains (Complex.exp z) := by
  have hscale : (scale (1/(2^s : ℚ)) b).Contains (z/(2^s : ℂ)) := by
    convert scale_contains hb (1/(2^s : ℚ)) using 1
    push_cast
    ring
  have h := repeatedSquare_contains (expTaylor_contains hscale prec n hg) prec s
  have he : Complex.exp (z/(2^s : ℂ))^(2^s) = Complex.exp z := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  simpa only [expScaled, he] using h

end ComplexBall
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ComplexBall.expScaled_contains
