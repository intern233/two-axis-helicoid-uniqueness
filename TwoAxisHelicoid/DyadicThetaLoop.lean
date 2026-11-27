import TwoAxisHelicoid.DyadicThetaTerm

namespace TwoAxisHelicoid

structure DyadicThetaState where
  sum : DyadicBall
  coefficient : DyadicBall
  step : DyadicBall
  positive : DyadicBall
  negative : DyadicBall
  deriving Repr

inductive DyadicThetaLoop where
  | zero
  | step (previous : DyadicThetaLoop) (term : DyadicExpressionTrace) (next : DyadicThetaState)
  deriving Repr

namespace DyadicThetaLoop

def length : DyadicThetaLoop → ℕ
  | .zero => 0
  | .step p _ _ => p.length+1

def state (prec : ℕ) (bq bp bm : DyadicBall) : DyadicThetaLoop → DyadicThetaState
  | .zero => ⟨DyadicBall.zero, DyadicBall.one prec, bq, bp, bm⟩
  | .step _ _ s => s

def Valid (cfg : BallConfig) (j : ℕ) (bq bp bm bp2 bm2 : DyadicBall) : DyadicThetaLoop → Prop
  | .zero => True
  | .step p term next =>
    let s := p.state cfg.prec bq bp bm
    p.Valid cfg j bq bp bm bp2 bm2 ∧
    term.Valid cfg (threeDyadic s.coefficient s.positive s.negative)
      (thetaSeedTermExpression j p.length) ∧
    DyadicBall.ChecksAdd next.sum s.sum term.output ∧
    DyadicBall.ChecksMul cfg.prec next.coefficient s.coefficient s.step ∧
    DyadicBall.ChecksMul cfg.prec next.step s.step bq ∧
    DyadicBall.ChecksMul cfg.prec next.positive s.positive bp2 ∧
    DyadicBall.ChecksMul cfg.prec next.negative s.negative bm2

instance instDecidableValid (cfg : BallConfig) (j : ℕ) (bq bp bm bp2 bm2 : DyadicBall)
    (w : DyadicThetaLoop) : Decidable (w.Valid cfg j bq bp bm bp2 bm2) :=
  match w with
  | .zero => instDecidableTrue
  | .step p term next => by
    haveI := instDecidableValid cfg j bq bp bm bp2 bm2 p
    unfold Valid
    infer_instance

def StateContains (prec j n : ℕ) (t : ℝ) (v : ℂ) (s : DyadicThetaState) : Prop :=
  (s.sum.toBall prec).Contains (∑ k ∈ Finset.range n, thetaTerm t j k v) ∧
  (s.coefficient.toBall prec).Contains (Complex.exp (-Real.pi*t*n*(n+1)/2)) ∧
  (s.step.toBall prec).Contains (Complex.exp (-Real.pi*t*(n+1))) ∧
  (s.positive.toBall prec).Contains (Complex.exp ((2*n+1 : ℂ)*v*Complex.I)) ∧
  (s.negative.toBall prec).Contains (Complex.exp (-((2*n+1 : ℂ)*v)*Complex.I))

theorem sound {bq bp bm bp2 bm2 : DyadicBall} {t : ℝ} {v : ℂ}
    (cfg : BallConfig) (j : ℕ)
    (hq : (bq.toBall cfg.prec).Contains (Complex.exp (-Real.pi*t)))
    (hp : (bp.toBall cfg.prec).Contains (Complex.exp (v*Complex.I)))
    (hm : (bm.toBall cfg.prec).Contains (Complex.exp (-v*Complex.I)))
    (hp2 : (bp2.toBall cfg.prec).Contains (Complex.exp (2*v*Complex.I)))
    (hm2 : (bm2.toBall cfg.prec).Contains (Complex.exp (-2*v*Complex.I)))
    (w : DyadicThetaLoop) (hw : w.Valid cfg j bq bp bm bp2 bm2) :
    StateContains cfg.prec j w.length t v (w.state cfg.prec bq bp bm) := by
  induction w with
  | zero =>
    exact ⟨by simpa [state, length] using DyadicBall.zero_contains cfg.prec,
      by simpa [state, length] using DyadicBall.one_contains cfg.prec,
      by simpa [state, length] using hq,
      by simpa [state, length] using hp,
      by simpa [state, length] using hm⟩
  | step p term next ih =>
    rcases hw with ⟨hprev, hterm, hsum, hcoeff, hstep, hpos, hneg⟩
    rcases ih hprev with ⟨hs, hc, hst, hp', hm'⟩
    have ht := dyadic_thetaTerm_contains cfg j p.length term hc hp' hm' hterm
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [length, state, Finset.sum_range_succ] using
        DyadicBall.add_contains hs ht hsum
    · have h := DyadicBall.mul_contains hc hst hcoeff
      change (next.coefficient.toBall cfg.prec).Contains _
      convert h using 1
      rw [← Complex.exp_add]
      congr 1
      simp only [length, Nat.cast_add, Nat.cast_one]
      ring
    · have h := DyadicBall.mul_contains hst hq hstep
      change (next.step.toBall cfg.prec).Contains _
      convert h using 1
      rw [← Complex.exp_add]
      congr 1
      simp only [length, Nat.cast_add, Nat.cast_one]
      ring
    · have h := DyadicBall.mul_contains hp' hp2 hpos
      change (next.positive.toBall cfg.prec).Contains _
      convert h using 1
      rw [← Complex.exp_add]
      congr 1
      simp only [length, Nat.cast_add, Nat.cast_one]
      ring
    · have h := DyadicBall.mul_contains hm' hm2 hneg
      change (next.negative.toBall cfg.prec).Contains _
      convert h using 1
      rw [← Complex.exp_add]
      congr 1
      simp only [length, Nat.cast_add, Nat.cast_one]
      ring

end DyadicThetaLoop
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicThetaLoop.sound
