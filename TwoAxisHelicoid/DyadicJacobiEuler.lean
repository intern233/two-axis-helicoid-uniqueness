import TwoAxisHelicoid.DyadicJacobiProduct
import TwoAxisHelicoid.JacobiFiniteEuler

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000

def jacobiEulerTermExpression : BallExpression :=
  .div (.neg (.input 0)) (.sub (.rational 1) (.input 0))

theorem value_jacobiEulerTermExpression (z : ℂ) :
    jacobiEulerTermExpression.value (threeValues z 0 0) = -z/(1-z) := by
  simp only [jacobiEulerTermExpression, BallExpression.value_div,
    BallExpression.value_sub, BallExpression.value, BallExpression.value_rational,
    threeValues, Rat.cast_one]

structure DyadicJacobiEulerState where
  sum : DyadicBall
  term : DyadicBall
  deriving Repr

inductive DyadicJacobiEulerLoop where
  | zero
  | step (previous : DyadicJacobiEulerLoop) (summand : DyadicExpressionTrace)
      (next : DyadicJacobiEulerState)
  deriving Repr

namespace DyadicJacobiEulerLoop

def length : DyadicJacobiEulerLoop → ℕ
  | .zero => 0
  | .step p _ _ => p.length+1

def state (bz : DyadicBall) : DyadicJacobiEulerLoop → DyadicJacobiEulerState
  | .zero => ⟨.zero, bz⟩
  | .step _ _ s => s

def Valid (cfg : BallConfig) (bq bz : DyadicBall) : DyadicJacobiEulerLoop → Prop
  | .zero => True
  | .step p summand next =>
    let s := p.state bz
    p.Valid cfg bq bz ∧
    summand.Valid cfg (threeDyadic s.term .zero .zero) jacobiEulerTermExpression ∧
    DyadicBall.ChecksAdd next.sum s.sum summand.output ∧
    DyadicBall.ChecksMul cfg.prec next.term s.term bq

instance instDecidableValid (cfg : BallConfig) (bq bz : DyadicBall)
    (w : DyadicJacobiEulerLoop) : Decidable (w.Valid cfg bq bz) :=
  match w with
  | .zero => instDecidableTrue
  | .step p summand next => by
    haveI := instDecidableValid cfg bq bz p
    unfold Valid
    infer_instance

theorem sound {bq bz : DyadicBall} {Q x : ℂ} (cfg : BallConfig)
    (hq : (bq.toBall cfg.prec).Contains Q) (hz : (bz.toBall cfg.prec).Contains (Q*x))
    (w : DyadicJacobiEulerLoop) (hw : w.Valid cfg bq bz) :
    ((w.state bz).sum.toBall cfg.prec).Contains (jacobiFiniteEuler Q x w.length) ∧
    ((w.state bz).term.toBall cfg.prec).Contains (Q^(w.length+1)*x) := by
  induction w with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa [state, length, jacobiFiniteEuler] using DyadicBall.zero_contains cfg.prec
    · simpa [state, length] using hz
  | step p summand next ih =>
    rcases hw with ⟨hprev, hsummand, hsum, hterm⟩
    rcases ih hprev with ⟨hs, ht⟩
    have hz0 := DyadicBall.zero_contains cfg.prec
    have hf := summand.sound cfg _ _ (threeDyadic_contains ht hz0 hz0) _ hsummand
    rw [value_jacobiEulerTermExpression] at hf
    constructor
    · have h := DyadicBall.add_contains hs hf hsum
      simpa only [state, length, jacobiFiniteEuler, Finset.sum_range_succ, neg_mul] using h
    · have h := DyadicBall.mul_contains ht hq hterm
      change (next.term.toBall cfg.prec).Contains _
      convert h using 1
      simp only [length, pow_succ]
      ring

end DyadicJacobiEulerLoop

structure DyadicJacobiEulerTrace where
  loop : DyadicJacobiEulerLoop
  output : DyadicBall
  deriving Repr

namespace DyadicJacobiEulerTrace

def Valid (cfg : BallConfig) (err : ℕ) (bq bz : DyadicBall) (w : DyadicJacobiEulerTrace) : Prop :=
  let s := w.loop.state bz
  let σ := bq.normUpper cfg.prec
  let τ := s.term.normUpper cfg.prec
  w.loop.Valid cfg bq bz ∧ σ < 1 ∧ bz.normUpper cfg.prec < 1 ∧ τ < 1 ∧
    τ/((1-σ)*(1-τ)) ≤ (err : ℚ)/DyadicBall.denominator cfg.prec ∧
    w.output.Coarsens (s.sum.inflate err)

instance (cfg : BallConfig) (err : ℕ) (bq bz : DyadicBall) (w : DyadicJacobiEulerTrace) :
    Decidable (w.Valid cfg err bq bz) := by unfold Valid; infer_instance

theorem sound {bq bz : DyadicBall} {Q x : ℂ} (cfg : BallConfig) (err : ℕ)
    (hq : (bq.toBall cfg.prec).Contains Q) (hz : (bz.toBall cfg.prec).Contains (Q*x))
    (w : DyadicJacobiEulerTrace) (hw : w.Valid cfg err bq bz) :
    (w.output.toBall cfg.prec).Contains (x*logDeriv (jacobiFactorProduct Q) x) := by
  rcases hw with ⟨hloop, hσ, hx, hτ, herr, hout⟩
  have hs := w.loop.sound cfg hq hz hloop
  have hx' : ‖Q‖*‖x‖ < 1 := by
    rw [← norm_mul]
    exact (DyadicBall.norm_le_normUpper hz).trans_lt (by exact_mod_cast hx)
  have he := jacobiEulerLog_finite_error
    (DyadicBall.norm_le_normUpper hq) (by exact_mod_cast hσ) hx'
    (DyadicBall.norm_le_normUpper hs.2) (by exact_mod_cast hτ)
  have herr' : ((w.loop.state bz).term.normUpper cfg.prec : ℝ)/
      ((1-(bq.normUpper cfg.prec : ℝ))*(1-((w.loop.state bz).term.normUpper cfg.prec : ℝ))) ≤
        (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ) := by exact_mod_cast herr
  exact DyadicBall.coarsen_contains (DyadicBall.inflate_contains hs.1 (he.trans herr')) hout

end DyadicJacobiEulerTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicJacobiEulerTrace.sound
