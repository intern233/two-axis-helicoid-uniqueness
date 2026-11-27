import TwoAxisHelicoid.DyadicJacobiProduct
import TwoAxisHelicoid.JacobiFiniteSecond

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000

def jacobiSecondTermExpression : BallExpression :=
  .div (.input 0) (.pow (.sub (.rational 1) (.input 0)) 2)

theorem value_jacobiSecondTermExpression (z : ℝ) :
    jacobiSecondTermExpression.value (threeValues z 0 0) = (jacobiFraction z : ℂ) := by
  simp only [jacobiSecondTermExpression, BallExpression.value_div, BallExpression.value_pow,
    BallExpression.value_sub, BallExpression.value, BallExpression.value_rational,
    threeValues, Rat.cast_one, jacobiFraction, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_sub, Complex.ofReal_one]

structure DyadicJacobiSecondState where
  sum : DyadicBall
  term : DyadicBall
  deriving Repr

inductive DyadicJacobiSecondLoop where
  | zero
  | step (previous : DyadicJacobiSecondLoop) (summand : DyadicExpressionTrace)
      (next : DyadicJacobiSecondState)
  deriving Repr

namespace DyadicJacobiSecondLoop

def length : DyadicJacobiSecondLoop → ℕ
  | .zero => 0
  | .step p _ _ => p.length+1

def state (bz : DyadicBall) : DyadicJacobiSecondLoop → DyadicJacobiSecondState
  | .zero => ⟨.zero, bz⟩
  | .step _ _ s => s

def Valid (cfg : BallConfig) (bq bz : DyadicBall) : DyadicJacobiSecondLoop → Prop
  | .zero => True
  | .step p summand next =>
    let s := p.state bz
    p.Valid cfg bq bz ∧
    summand.Valid cfg (threeDyadic s.term .zero .zero) jacobiSecondTermExpression ∧
    DyadicBall.ChecksAdd next.sum s.sum summand.output ∧
    DyadicBall.ChecksMul cfg.prec next.term s.term bq

instance instDecidableValid (cfg : BallConfig) (bq bz : DyadicBall)
    (w : DyadicJacobiSecondLoop) : Decidable (w.Valid cfg bq bz) :=
  match w with
  | .zero => instDecidableTrue
  | .step p summand next => by
    haveI := instDecidableValid cfg bq bz p
    unfold Valid
    infer_instance

theorem sound {bq bz : DyadicBall} {Q a : ℝ} (cfg : BallConfig)
    (hq : (bq.toBall cfg.prec).Contains (Q : ℂ)) (hz : (bz.toBall cfg.prec).Contains (a : ℂ))
    (w : DyadicJacobiSecondLoop) (hw : w.Valid cfg bq bz) :
    ((w.state bz).sum.toBall cfg.prec).Contains (jacobiFiniteSecond Q a w.length : ℂ) ∧
    ((w.state bz).term.toBall cfg.prec).Contains (Q^w.length*a : ℝ) := by
  induction w with
  | zero =>
    refine ⟨?_, ?_⟩
    · simpa [state, length, jacobiFiniteSecond] using DyadicBall.zero_contains cfg.prec
    · simpa [state, length] using hz
  | step p summand next ih =>
    rcases hw with ⟨hprev, hsummand, hsum, hterm⟩
    rcases ih hprev with ⟨hs, ht⟩
    have hz0 := DyadicBall.zero_contains cfg.prec
    have hf := summand.sound cfg _ _ (threeDyadic_contains ht hz0 hz0) _ hsummand
    rw [value_jacobiSecondTermExpression] at hf
    constructor
    · have h := DyadicBall.add_contains hs hf hsum
      simpa only [state, length, jacobiFiniteSecond, Finset.sum_range_succ, Complex.ofReal_add] using h
    · have h := DyadicBall.mul_contains ht hq hterm
      change (next.term.toBall cfg.prec).Contains _
      convert h using 1
      simp only [length, pow_succ]
      push_cast
      ring

end DyadicJacobiSecondLoop

structure DyadicJacobiSecondTrace where
  loop : DyadicJacobiSecondLoop
  output : DyadicBall
  deriving Repr

namespace DyadicJacobiSecondTrace

def Valid (cfg : BallConfig) (err : ℕ) (bq bz : DyadicBall) (w : DyadicJacobiSecondTrace) : Prop :=
  let s := w.loop.state bz
  let σ := bq.normUpper cfg.prec
  let τ := s.term.normUpper cfg.prec
  w.loop.Valid cfg bq bz ∧ σ < 1 ∧ bz.normUpper cfg.prec < 1 ∧ τ < 1 ∧
    τ/((1-σ)*(1-τ)^2) ≤ (err : ℚ)/DyadicBall.denominator cfg.prec ∧
    w.output.Coarsens (s.sum.inflate err)

instance (cfg : BallConfig) (err : ℕ) (bq bz : DyadicBall) (w : DyadicJacobiSecondTrace) :
    Decidable (w.Valid cfg err bq bz) := by unfold Valid; infer_instance

theorem sound {bq bz : DyadicBall} {Q a : ℝ} (cfg : BallConfig) (err : ℕ)
    (hq : (bq.toBall cfg.prec).Contains (Q : ℂ)) (hz : (bz.toBall cfg.prec).Contains (a : ℂ))
    (w : DyadicJacobiSecondTrace) (hw : w.Valid cfg err bq bz) :
    (w.output.toBall cfg.prec).Contains (jacobiGeometricSeries Q a : ℂ) := by
  rcases hw with ⟨hloop, hσ, ha, hτ, herr, hout⟩
  have hs := w.loop.sound cfg hq hz hloop
  have hQ := DyadicBall.norm_le_normUpper hq
  have hA := DyadicBall.norm_le_normUpper hz
  have hT := DyadicBall.norm_le_normUpper hs.2
  simp only [Complex.norm_real, Real.norm_eq_abs] at hQ hA hT
  have he := jacobiGeometricSeries_finite_error hQ (by exact_mod_cast hσ)
    (hA.trans_lt (by exact_mod_cast ha)) hT (by exact_mod_cast hτ)
  have herr' : ((w.loop.state bz).term.normUpper cfg.prec : ℝ)/
      ((1-(bq.normUpper cfg.prec : ℝ))*(1-((w.loop.state bz).term.normUpper cfg.prec : ℝ))^2) ≤
        (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ) := by exact_mod_cast herr
  have herror : ‖(jacobiGeometricSeries Q a : ℂ)-(jacobiFiniteSecond Q a w.loop.length : ℂ)‖ ≤
      (err : ℝ)/(DyadicBall.denominator cfg.prec : ℝ) := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using he.trans herr'
  exact DyadicBall.coarsen_contains (DyadicBall.inflate_contains hs.1 herror) hout

end DyadicJacobiSecondTrace
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.DyadicJacobiSecondTrace.sound
