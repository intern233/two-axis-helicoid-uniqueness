import TwoAxisHelicoid.TraceDataBridge

namespace TwoAxisHelicoid.TraceData

namespace BallConfig
@[simp] theorem interpret_prec (cfg : BallConfig) : cfg.interpret.prec = cfg.prec := rfl
@[simp] theorem interpret_terms (cfg : BallConfig) : cfg.interpret.terms = cfg.terms := rfl
@[simp] theorem interpret_squarings (cfg : BallConfig) : cfg.interpret.squarings = cfg.squarings := rfl
end BallConfig

theorem factorial_eq (n : ℕ) : factorial n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [factorial, Nat.factorial, ih]

theorem rat_abs_eq (q : ℚ) : Rat.abs q = |q| := by
  unfold Rat.abs
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (lt_of_not_ge h)).symm

namespace DyadicBall

@[simp] theorem interpret_ChecksAdd (out a b : DyadicBall) :
    TwoAxisHelicoid.DyadicBall.ChecksAdd out.interpret a.interpret b.interpret ↔ ChecksAdd out a b := by
  simp only [TwoAxisHelicoid.DyadicBall.ChecksAdd, ChecksAdd, interpret, Int.abs_eq_natAbs]
  rfl
@[simp] theorem interpret_ChecksMul (prec : ℕ) (out a b : DyadicBall) :
    TwoAxisHelicoid.DyadicBall.ChecksMul prec out.interpret a.interpret b.interpret ↔ ChecksMul prec out a b := by
  simp only [TwoAxisHelicoid.DyadicBall.ChecksMul, ChecksMul, interpret, Int.abs_eq_natAbs]
  rfl
@[simp] theorem interpret_ChecksDivNat (out a : DyadicBall) (n : ℕ) :
    TwoAxisHelicoid.DyadicBall.ChecksDivNat out.interpret a.interpret n ↔ ChecksDivNat out a n := by
  simp only [TwoAxisHelicoid.DyadicBall.ChecksDivNat, ChecksDivNat, interpret, Int.abs_eq_natAbs]
  rfl
@[simp] theorem interpret_ChecksInv (prec : ℕ) (out a : DyadicBall) :
    TwoAxisHelicoid.DyadicBall.ChecksInv prec out.interpret a.interpret ↔ ChecksInv prec out a := by
  simp only [TwoAxisHelicoid.DyadicBall.ChecksInv, ChecksInv, interpret, Int.abs_eq_natAbs, TwoAxisHelicoid.DyadicBall.lower, lower]
  rfl
@[simp] theorem interpret_ChecksPoint (prec : ℕ) (out : DyadicBall) (c : QComplex) :
    TwoAxisHelicoid.DyadicBall.ChecksPoint prec out.interpret c.interpret ↔ ChecksPoint prec out c := by
  simp only [TwoAxisHelicoid.DyadicBall.ChecksPoint, ChecksPoint, interpret, Int.abs_eq_natAbs]
  rfl
@[simp] theorem interpret_Coarsens (out a : DyadicBall) :
    TwoAxisHelicoid.DyadicBall.Coarsens out.interpret a.interpret ↔ Coarsens out a := by
  simp only [TwoAxisHelicoid.DyadicBall.Coarsens, Coarsens, interpret, Int.abs_eq_natAbs]
  rfl
@[simp] theorem interpret_neg (a : DyadicBall) : a.interpret.neg = a.neg.interpret := rfl
@[simp] theorem interpret_inflate (a : DyadicBall) (err : ℕ) :
    a.interpret.inflate err = (a.inflate err).interpret := rfl
@[simp] theorem interpret_lower (a : DyadicBall) : a.interpret.lower = a.lower := by
  simp only [TwoAxisHelicoid.DyadicBall.lower, lower, interpret, Int.abs_eq_natAbs]
  rfl
@[simp] theorem interpret_ChecksImOne (prec : ℕ) (a : DyadicBall) :
    a.interpret.ChecksImOne prec ↔ a.ChecksImOne prec := by
  simp only [TwoAxisHelicoid.DyadicBall.ChecksImOne, ChecksImOne, interpret, Int.abs_eq_natAbs]
  rfl
@[simp] theorem interpret_ChecksExpGuard (prec n : ℕ) (b : DyadicBall) :
    TwoAxisHelicoid.DyadicBall.ChecksExpGuard prec n b.interpret ↔ ChecksExpGuard prec n b := by
  simp only [TwoAxisHelicoid.DyadicBall.ChecksExpGuard, ChecksExpGuard, interpret, Int.abs_eq_natAbs, TwoAxisHelicoid.DyadicBall.upper, upper]
  rfl
@[simp] theorem interpret_ChecksExpError (prec n : ℕ) (out sum input : DyadicBall) :
    TwoAxisHelicoid.DyadicBall.ChecksExpError prec n out.interpret sum.interpret input.interpret ↔
      ChecksExpError prec n out sum input := by
  simp only [TwoAxisHelicoid.DyadicBall.ChecksExpError, ChecksExpError, interpret, Int.abs_eq_natAbs, TwoAxisHelicoid.DyadicBall.upper, upper, factorial_eq]
  rfl

end DyadicBall

namespace DyadicTaylorTrace

theorem interpret_check (prec : ℕ) (b : DyadicBall) (w : DyadicTaylorTrace) :
    w.interpret.check prec b.interpret = w.check prec b := by
  induction w with
  | zero => rfl
  | step p s m t ih =>
    simp only [interpret, check, TwoAxisHelicoid.DyadicTaylorTrace.check, ih,
      interpret_sum, interpret_term, interpret_length, DyadicBall.interpret_ChecksAdd,
      DyadicBall.interpret_ChecksMul, DyadicBall.interpret_ChecksDivNat]

end DyadicTaylorTrace

namespace DyadicSquareTrace

theorem interpret_check (prec : ℕ) (b : DyadicBall) (w : DyadicSquareTrace) :
    w.interpret.check prec b.interpret = w.check prec b := by
  induction w with
  | zero => rfl
  | step p out ih =>
    simp only [interpret, check, TwoAxisHelicoid.DyadicSquareTrace.check, ih,
      interpret_output, DyadicBall.interpret_ChecksMul]

end DyadicSquareTrace

namespace DyadicExpTrace

theorem interpret_check (cfg : BallConfig) (b : DyadicBall) (w : DyadicExpTrace) :
    w.interpret.check cfg.interpret b.interpret = w.check cfg b := by
  simp only [interpret, check, TwoAxisHelicoid.DyadicExpTrace.check, BallConfig.interpret_prec, BallConfig.interpret_terms, BallConfig.interpret_squarings,
    DyadicBall.interpret_ChecksDivNat, DyadicTaylorTrace.interpret_length,
    DyadicTaylorTrace.interpret_check, DyadicTaylorTrace.interpret_sum,
    DyadicBall.interpret_ChecksExpGuard, DyadicBall.interpret_ChecksExpError,
    DyadicSquareTrace.interpret_length, DyadicSquareTrace.interpret_check]

end DyadicExpTrace

namespace DyadicExpressionTrace

theorem interpret_check (cfg : BallConfig) (env : ℕ → DyadicBall)
    (e : BallExpression) (w : DyadicExpressionTrace) :
    w.interpret.check cfg.interpret (fun i => (env i).interpret) e.interpret = w.check cfg env e := by
  induction e generalizing w <;> cases w <;>
    simp_all only [interpret, BallExpression.interpret, check, TwoAxisHelicoid.DyadicExpressionTrace.check,
      interpret_output, BallConfig.interpret_prec, DyadicBall.interpret_ChecksPoint,
      DyadicBall.interpret_Coarsens, DyadicBall.interpret_neg, DyadicBall.interpret_ChecksAdd,
      DyadicBall.interpret_ChecksMul, DyadicBall.interpret_ChecksInv, DyadicExpTrace.interpret_check]
  simp only [TwoAxisHelicoid.ComplexBall.coarsens, TwoAxisHelicoid.QComplex.absUpper, TwoAxisHelicoid.QComplex.sub,
    TwoAxisHelicoid.QComplex.add, TwoAxisHelicoid.QComplex.neg, TwoAxisHelicoid.DyadicBall.toBall, DyadicBall.interpret,
    TwoAxisHelicoid.ComplexBall.piBall, TwoAxisHelicoid.ComplexBall.realInterval, TwoAxisHelicoid.QComplex.ofRat,
    ComplexBall.coarsens, QComplex.absUpper, QComplex.sub, QComplex.add, QComplex.neg,
    DyadicBall.toBall, ComplexBall.piBall, ComplexBall.realInterval, QComplex.ofRat, rat_abs_eq]
  rfl

end DyadicExpressionTrace

theorem interpret_threeDyadic (a b c : DyadicBall) :
    (fun i => (threeDyadic a b c i).interpret) = TwoAxisHelicoid.threeDyadic a.interpret b.interpret c.interpret := by
  funext i
  rcases i with _ | (_ | (_ | i)) <;> rfl

theorem interpret_fiveDyadic (a b c d e : DyadicBall) :
    (fun i => (fiveDyadic a b c d e i).interpret) =
      TwoAxisHelicoid.fiveDyadic a.interpret b.interpret c.interpret d.interpret e.interpret := by
  funext i
  rcases i with _ | (_ | (_ | (_ | (_ | i)))) <;> rfl

@[simp] theorem interpret_thetaSeedTermExpression (j n : ℕ) :
    (thetaSeedTermExpression j n).interpret = TwoAxisHelicoid.thetaSeedTermExpression j n := by
  simp only [thetaSeedTermExpression, TwoAxisHelicoid.thetaSeedTermExpression,
    BallExpression.interpret, BallExpression.interpret_rational, BallExpression.interpret_div,
    BallExpression.interpret_pow, BallExpression.interpret_sub]
  rfl

namespace DyadicThetaLoop

theorem interpret_check (cfg : BallConfig) (j : ℕ) (bq bp bm bp2 bm2 : DyadicBall)
    (w : DyadicThetaLoop) :
    w.interpret.check cfg.interpret j bq.interpret bp.interpret bm.interpret bp2.interpret bm2.interpret =
      w.check cfg j bq bp bm bp2 bm2 := by
  induction w with
  | zero => rfl
  | step p term next ih =>
    simp only [interpret, check, TwoAxisHelicoid.DyadicThetaLoop.check, interpret_state, interpret_length,
      DyadicThetaState.interpret, ih, BallConfig.interpret_prec]
    rw [← interpret_threeDyadic, ← interpret_thetaSeedTermExpression]
    simp only [DyadicExpressionTrace.interpret_check, DyadicBall.interpret_ChecksAdd,
      DyadicBall.interpret_ChecksMul, DyadicExpressionTrace.interpret_output]

end DyadicThetaLoop

namespace DyadicThetaSeed

theorem interpret_check (cfg : BallConfig) (bv : DyadicBall) (w : DyadicThetaSeed) :
    w.interpret.check cfg.interpret bv.interpret = w.check cfg bv := by
  simp only [interpret, check, TwoAxisHelicoid.DyadicThetaSeed.check, BallConfig.interpret_prec]
  have he : TwoAxisHelicoid.threeDyadic bv.interpret .zero .zero =
      (fun i => (threeDyadic bv .zero .zero i).interpret) := (interpret_threeDyadic bv .zero .zero).symm
  rw [he]
  change (w.positive.interpret.check cfg.interpret _ thetaPositiveSeedExpression.interpret &&
    w.negative.interpret.check cfg.interpret _ thetaNegativeSeedExpression.interpret && _ && _) = _
  simp only [DyadicExpressionTrace.interpret_check, DyadicExpressionTrace.interpret_output,
    DyadicBall.interpret_ChecksMul]

end DyadicThetaSeed

namespace DyadicThetaTrace

theorem interpret_check (cfg : BallConfig) (j N err : ℕ) (bq : DyadicBall)
    (seed : DyadicThetaSeed) (w : DyadicThetaTrace) :
    w.interpret.check cfg.interpret j N err bq.interpret seed.interpret =
      w.check cfg j N err bq seed := by
  simp only [interpret, check, TwoAxisHelicoid.DyadicThetaTrace.check, DyadicThetaSeed.interpret,
    DyadicThetaLoop.interpret_length, DyadicExpressionTrace.interpret_output,
    DyadicThetaLoop.interpret_check, DyadicThetaLoop.interpret_state,
    DyadicThetaState.interpret, DyadicBall.interpret_inflate, DyadicBall.interpret_Coarsens,
    BallConfig.interpret_prec]

end DyadicThetaTrace
end TwoAxisHelicoid.TraceData

#print axioms TwoAxisHelicoid.TraceData.DyadicThetaTrace.interpret_check
