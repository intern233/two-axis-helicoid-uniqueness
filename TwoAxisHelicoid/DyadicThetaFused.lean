import TwoAxisHelicoid.DyadicThetaTrace

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000

def thetaFusedTermExpression (j n : ℕ) : BallExpression :=
  .mul
    (.mul (.rational ((if n%4<2 then 1 else -1)*(2*n+1 : ℚ)^j))
      (.div (.pow (.const ⟨0,1⟩) j) (.const ⟨0,2⟩)))
    (.sub (.input 0) (.mul (.rational ((-1 : ℚ)^j)) (.input 1)))

noncomputable def thetaFusedPositive (t : ℝ) (n : ℕ) (v : ℂ) : ℂ :=
  Complex.exp (-Real.pi*t*n*(n+1)/2+(2*n+1 : ℂ)*v*I)
noncomputable def thetaFusedNegative (t : ℝ) (n : ℕ) (v : ℂ) : ℂ :=
  Complex.exp (-Real.pi*t*n*(n+1)/2+(-((2*n+1 : ℂ)*v))*I)

theorem value_thetaFusedTermExpression (t : ℝ) (v : ℂ) (j n : ℕ) :
    (thetaFusedTermExpression j n).value
      (threeValues (thetaFusedPositive t n v) (thetaFusedNegative t n v) 0) =
      thetaTerm t j n v := by
  have hI : (⟨0,1⟩ : QComplex).val = I := by
    apply Complex.ext <;> norm_num [QComplex.val]
  have h2I : (⟨0,2⟩ : QComplex).val = 2*I := by
    apply Complex.ext <;> norm_num [QComplex.val]
  simp only [thetaFusedTermExpression, BallExpression.value, BallExpression.value_rational,
    BallExpression.value_div, BallExpression.value_sub, BallExpression.value_pow,
    threeValues, hI, h2I, thetaFusedPositive, thetaFusedNegative, Complex.exp_add]
  unfold thetaTerm sineJet thetaSign
  rw [Complex.ofReal_exp]
  push_cast
  split_ifs <;> ring

structure DyadicThetaFusedState where
  sum : DyadicBall
  positive : DyadicBall
  negative : DyadicBall
  positiveRatio : DyadicBall
  negativeRatio : DyadicBall
  deriving Repr

inductive DyadicThetaFusedLoop where
  | zero
  | step (previous : DyadicThetaFusedLoop) (term : DyadicExpressionTrace)
      (next : DyadicThetaFusedState)
  deriving Repr

namespace DyadicThetaFusedLoop

def length : DyadicThetaFusedLoop → ℕ
  | .zero => 0
  | .step p _ _ => p.length+1

def state (bp bm brp brm : DyadicBall) : DyadicThetaFusedLoop → DyadicThetaFusedState
  | .zero => ⟨.zero, bp, bm, brp, brm⟩
  | .step _ _ s => s

def Valid (cfg : BallConfig) (j : ℕ) (bq bp bm brp brm : DyadicBall) :
    DyadicThetaFusedLoop → Prop
  | .zero => True
  | .step p term next =>
    let s := p.state bp bm brp brm
    p.Valid cfg j bq bp bm brp brm ∧
    term.Valid cfg (threeDyadic s.positive s.negative .zero)
      (thetaFusedTermExpression j p.length) ∧
    DyadicBall.ChecksAdd next.sum s.sum term.output ∧
    DyadicBall.ChecksMul cfg.prec next.positive s.positive s.positiveRatio ∧
    DyadicBall.ChecksMul cfg.prec next.negative s.negative s.negativeRatio ∧
    DyadicBall.ChecksMul cfg.prec next.positiveRatio s.positiveRatio bq ∧
    DyadicBall.ChecksMul cfg.prec next.negativeRatio s.negativeRatio bq

instance instDecidableValid (cfg : BallConfig) (j : ℕ) (bq bp bm brp brm : DyadicBall)
    (w : DyadicThetaFusedLoop) : Decidable (w.Valid cfg j bq bp bm brp brm) :=
  match w with
  | .zero => instDecidableTrue
  | .step p term next => by
    haveI := instDecidableValid cfg j bq bp bm brp brm p
    unfold Valid
    infer_instance

def StateContains (prec j n : ℕ) (t : ℝ) (v : ℂ) (s : DyadicThetaFusedState) : Prop :=
  (s.sum.toBall prec).Contains (∑ k ∈ Finset.range n, thetaTerm t j k v) ∧
  (s.positive.toBall prec).Contains (thetaFusedPositive t n v) ∧
  (s.negative.toBall prec).Contains (thetaFusedNegative t n v) ∧
  (s.positiveRatio.toBall prec).Contains (Complex.exp (-Real.pi*t*(n+1)+2*v*I)) ∧
  (s.negativeRatio.toBall prec).Contains (Complex.exp (-Real.pi*t*(n+1)-2*v*I))

theorem sound {bq bp bm brp brm : DyadicBall} {t : ℝ} {v : ℂ}
    (cfg : BallConfig) (j : ℕ)
    (hq : (bq.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t)))
    (hp : (bp.toBall cfg.prec).Contains (Complex.exp (v*I)))
    (hm : (bm.toBall cfg.prec).Contains (Complex.exp (-v*I)))
    (hrp : (brp.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t+2*v*I)))
    (hrm : (brm.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t-2*v*I)))
    (w : DyadicThetaFusedLoop) (hw : w.Valid cfg j bq bp bm brp brm) :
    StateContains cfg.prec j w.length t v (w.state bp bm brp brm) := by
  induction w with
  | zero =>
    refine ⟨by simpa [state, length] using DyadicBall.zero_contains cfg.prec,
      ?_, ?_, ?_, ?_⟩
    · simpa [state, length, thetaFusedPositive] using hp
    · simpa [state, length, thetaFusedNegative] using hm
    · simpa [state, length] using hrp
    · simpa [state, length] using hrm
  | step p term next ih =>
    rcases hw with ⟨hprev, hterm, hsum, hpos, hneg, hrpos, hrneg⟩
    rcases ih hprev with ⟨hs, hp', hm', hrp', hrm'⟩
    have ht := term.sound cfg _ _ (threeDyadic_contains hp' hm' (DyadicBall.zero_contains cfg.prec))
      _ hterm
    rw [value_thetaFusedTermExpression] at ht
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [length, state, Finset.sum_range_succ] using
        DyadicBall.add_contains hs ht hsum
    · have h := DyadicBall.mul_contains hp' hrp' hpos
      change (next.positive.toBall cfg.prec).Contains _
      convert h using 1
      rw [thetaFusedPositive, thetaFusedPositive, ← Complex.exp_add]
      congr 1
      simp only [length, Nat.cast_add, Nat.cast_one]
      ring
    · have h := DyadicBall.mul_contains hm' hrm' hneg
      change (next.negative.toBall cfg.prec).Contains _
      convert h using 1
      rw [thetaFusedNegative, thetaFusedNegative, ← Complex.exp_add]
      congr 1
      simp only [length, Nat.cast_add, Nat.cast_one]
      ring
    · have h := DyadicBall.mul_contains hrp' hq hrpos
      change (next.positiveRatio.toBall cfg.prec).Contains _
      convert h using 1
      rw [← Complex.exp_add]
      congr 1
      simp only [length, Nat.cast_add, Nat.cast_one]
      ring
    · have h := DyadicBall.mul_contains hrm' hq hrneg
      change (next.negativeRatio.toBall cfg.prec).Contains _
      convert h using 1
      rw [← Complex.exp_add]
      congr 1
      simp only [length, Nat.cast_add, Nat.cast_one]
      ring

end DyadicThetaFusedLoop
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicThetaFusedLoop.sound
