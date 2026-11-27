import Init.Data.Rat

/- Pure finite certificate data. The analytic interpretation is proved in TraceDataBridge. -/
namespace TwoAxisHelicoid.TraceData

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1)*factorial n

structure QComplex where
  re : Rat
  im : Rat
  deriving DecidableEq, Repr

namespace QComplex

def ofRat (q : Rat) : QComplex := ⟨q, 0⟩

def add (c d : QComplex) : QComplex := ⟨c.re+d.re, c.im+d.im⟩

def neg (c : QComplex) : QComplex := ⟨-c.re, -c.im⟩

def sub (c d : QComplex) : QComplex := add c (neg d)

def mul (c d : QComplex) : QComplex := ⟨c.re*d.re-c.im*d.im, c.re*d.im+c.im*d.re⟩

def absUpper (c : QComplex) : Rat := Rat.abs c.re+Rat.abs c.im

end QComplex

structure ComplexBall where
  center : QComplex
  radius : Rat
  deriving DecidableEq, Repr

namespace ComplexBall

def point (c : QComplex) : ComplexBall := ⟨c, 0⟩

def add (a b : ComplexBall) : ComplexBall := ⟨a.center.add b.center, a.radius+b.radius⟩

def neg (a : ComplexBall) : ComplexBall := ⟨a.center.neg, a.radius⟩

def sub (a b : ComplexBall) : ComplexBall := add a (neg b)

def coarsens (b a : ComplexBall) : Prop :=
  (a.center.sub b.center).absUpper+a.radius ≤ b.radius

def rational (q : Rat) : ComplexBall := point (QComplex.ofRat q)

instance (b a : ComplexBall) : Decidable (coarsens b a) := inferInstanceAs
  (Decidable ((a.center.sub b.center).absUpper+a.radius ≤ b.radius))

def realInterval (lo hi : Rat) : ComplexBall :=
  ⟨QComplex.ofRat ((lo+hi)/2), (hi-lo)/2⟩

def piBall : ComplexBall :=
  realInterval (314159265358979323846/10^20) (314159265358979323847/10^20)

end ComplexBall

structure BallConfig where
  prec : Nat := 112
  terms : Nat := 24
  squarings : Nat := 16
  deriving DecidableEq, Repr

inductive BallExpression where
  | const (c : QComplex)
  | input (n : Nat)
  | pi
  | add (a b : BallExpression)
  | neg (a : BallExpression)
  | mul (a b : BallExpression)
  | inv (a : BallExpression)
  | exp (a : BallExpression)
  deriving DecidableEq, Repr

namespace BallExpression

def rational (q : Rat) : BallExpression := .const (QComplex.ofRat q)

def sub (a b : BallExpression) : BallExpression := .add a (.neg b)

def div (a b : BallExpression) : BallExpression := .mul a (.inv b)

def pow (a : BallExpression) : Nat → BallExpression
  | 0 => rational 1
  | n+1 => .mul (pow a n) a

def imaginaryUnit : BallExpression := .const ⟨0, 1⟩

end BallExpression

structure DyadicBall where
  re : Int
  im : Int
  radius : Nat
  deriving DecidableEq, Repr

namespace DyadicBall

def denominator (prec : Nat) : Int := 2^prec

def toBall (prec : Nat) (b : DyadicBall) : ComplexBall :=
  ⟨⟨(b.re : Rat)/(denominator prec : Rat), (b.im : Rat)/(denominator prec : Rat)⟩,
    (b.radius : Rat)/(denominator prec : Rat)⟩

def ChecksAdd (out a b : DyadicBall) : Prop :=
  (Int.ofNat (Int.natAbs (out.re-(a.re+b.re))))+(Int.ofNat (Int.natAbs (out.im-(a.im+b.im))))+(a.radius : Int)+b.radius ≤ out.radius

instance (out a b : DyadicBall) : Decidable (ChecksAdd out a b) := by
  unfold ChecksAdd
  infer_instance

def ChecksMul (prec : Nat) (out a b : DyadicBall) : Prop :=
  (Int.ofNat (Int.natAbs (out.re*denominator prec-(a.re*b.re-a.im*b.im))))+
    (Int.ofNat (Int.natAbs (out.im*denominator prec-(a.re*b.im+a.im*b.re))))+
    ((Int.ofNat (Int.natAbs (a.re)))+(Int.ofNat (Int.natAbs (a.im))))*(b.radius : Int)+((Int.ofNat (Int.natAbs (b.re)))+(Int.ofNat (Int.natAbs (b.im))))*(a.radius : Int)+
      (a.radius : Int)*b.radius ≤ (out.radius : Int)*denominator prec

instance (prec : Nat) (out a b : DyadicBall) : Decidable (ChecksMul prec out a b) := by
  unfold ChecksMul
  infer_instance

def ChecksDivNat (out a : DyadicBall) (m : Nat) : Prop :=
  0 < m ∧ (Int.ofNat (Int.natAbs (out.re*m-a.re)))+(Int.ofNat (Int.natAbs (out.im*m-a.im)))+(a.radius : Int) ≤ (out.radius : Int)*m

instance (out a : DyadicBall) (m : Nat) : Decidable (ChecksDivNat out a m) := by
  unfold ChecksDivNat
  infer_instance

def upper (b : DyadicBall) : Int := (Int.ofNat (Int.natAbs (b.re)))+(Int.ofNat (Int.natAbs (b.im)))+b.radius

def ChecksExpGuard (prec n : Nat) (b : DyadicBall) : Prop :=
  2*b.upper ≤ denominator prec*(n+1)

instance (prec n : Nat) (b : DyadicBall) : Decidable (ChecksExpGuard prec n b) := by
  unfold ChecksExpGuard
  infer_instance

def ChecksExpError (prec n : Nat) (out sum input : DyadicBall) : Prop :=
  out.re = sum.re ∧ out.im = sum.im ∧ sum.radius ≤ out.radius ∧
    2*input.upper^n*denominator prec ≤
      ((out.radius : Int)-sum.radius)*(factorial n : Int)*(denominator prec)^n

instance (prec n : Nat) (out sum input : DyadicBall) : Decidable (ChecksExpError prec n out sum input) := by
  unfold ChecksExpError
  infer_instance

def lower (a : DyadicBall) : Int := max (Int.ofNat (Int.natAbs (a.re))) (Int.ofNat (Int.natAbs (a.im)))-a.radius

def ChecksInv (prec : Nat) (out a : DyadicBall) : Prop :=
  0 < a.lower ∧
    (Int.ofNat (Int.natAbs ((denominator prec)^2-(out.re*a.re-out.im*a.im))))+(Int.ofNat (Int.natAbs (out.re*a.im+out.im*a.re)))+
      ((Int.ofNat (Int.natAbs (out.re)))+(Int.ofNat (Int.natAbs (out.im))))*(a.radius : Int) ≤ (out.radius : Int)*a.lower

instance (prec : Nat) (out a : DyadicBall) : Decidable (ChecksInv prec out a) := by
  unfold ChecksInv
  infer_instance

def neg (a : DyadicBall) : DyadicBall := ⟨-a.re, -a.im, a.radius⟩

def Coarsens (out a : DyadicBall) : Prop :=
  (Int.ofNat (Int.natAbs (out.re-a.re)))+(Int.ofNat (Int.natAbs (out.im-a.im)))+(a.radius : Int) ≤ out.radius

instance (out a : DyadicBall) : Decidable (Coarsens out a) := by unfold Coarsens; infer_instance

def inflate (b : DyadicBall) (r : Nat) : DyadicBall := ⟨b.re, b.im, b.radius+r⟩

def ChecksImOne (prec : Nat) (b : DyadicBall) : Prop :=
  (Int.ofNat (Int.natAbs (b.im)))+(b.radius : Int) ≤ denominator prec

instance (prec : Nat) (b : DyadicBall) : Decidable (b.ChecksImOne prec) := by
  unfold ChecksImOne
  infer_instance

def ChecksPoint (prec : Nat) (out : DyadicBall) (c : QComplex) : Prop :=
  (Int.ofNat (Int.natAbs (out.re*(c.re.den : Int)-c.re.num*denominator prec))) *(c.im.den : Int)+
    (Int.ofNat (Int.natAbs (out.im*(c.im.den : Int)-c.im.num*denominator prec))) *(c.re.den : Int) ≤
      (out.radius : Int)*c.re.den*c.im.den

instance (prec : Nat) (out : DyadicBall) (c : QComplex) : Decidable (ChecksPoint prec out c) := by
  unfold ChecksPoint
  infer_instance

def zero : DyadicBall := ⟨0, 0, 0⟩

def one (prec : Nat) : DyadicBall := ⟨denominator prec, 0, 0⟩

end DyadicBall

inductive DyadicTaylorTrace where
  | zero
  | step (previous : DyadicTaylorTrace) (sum product term : DyadicBall)
  deriving Repr

namespace DyadicTaylorTrace

def length : DyadicTaylorTrace → Nat
  | .zero => 0
  | .step p _ _ _ => p.length+1

def sum : DyadicTaylorTrace → DyadicBall
  | .zero => DyadicBall.zero
  | .step _ s _ _ => s

def term (prec : Nat) : DyadicTaylorTrace → DyadicBall
  | .zero => DyadicBall.one prec
  | .step _ _ _ t => t

def check (prec : Nat) (b : DyadicBall) : DyadicTaylorTrace → Bool
  | .zero => true
  | .step p s m t => p.check prec b &&
      decide (DyadicBall.ChecksAdd s p.sum (p.term prec)) &&
      decide (DyadicBall.ChecksMul prec m (p.term prec) b) &&
      decide (DyadicBall.ChecksDivNat t m (p.length+1))

end DyadicTaylorTrace

inductive DyadicSquareTrace where
  | zero
  | step (previous : DyadicSquareTrace) (out : DyadicBall)
  deriving Repr

namespace DyadicSquareTrace

def length : DyadicSquareTrace → Nat
  | .zero => 0
  | .step p _ => p.length+1

def output (base : DyadicBall) : DyadicSquareTrace → DyadicBall
  | .zero => base
  | .step _ b => b

def check (prec : Nat) (b : DyadicBall) : DyadicSquareTrace → Bool
  | .zero => true
  | .step p out => p.check prec b &&
      decide (DyadicBall.ChecksMul prec out (p.output b) (p.output b))

end DyadicSquareTrace

structure DyadicExpTrace where
  scaled : DyadicBall
  taylor : DyadicTaylorTrace
  enclosure : DyadicBall
  squares : DyadicSquareTrace
  deriving Repr

namespace DyadicExpTrace

def output (w : DyadicExpTrace) : DyadicBall := w.squares.output w.enclosure

def check (cfg : BallConfig) (b : DyadicBall) (w : DyadicExpTrace) : Bool :=
  decide (DyadicBall.ChecksDivNat w.scaled b (2^cfg.squarings)) &&
  decide (w.taylor.length = cfg.terms) && w.taylor.check cfg.prec w.scaled &&
  decide (DyadicBall.ChecksExpGuard cfg.prec cfg.terms w.scaled) &&
  decide (DyadicBall.ChecksExpError cfg.prec cfg.terms w.enclosure w.taylor.sum w.scaled) &&
  decide (w.squares.length = cfg.squarings) && w.squares.check cfg.prec w.enclosure

end DyadicExpTrace

inductive DyadicExpressionTrace where
  | atom (out : DyadicBall)
  | unary (out : DyadicBall) (child : DyadicExpressionTrace)
  | binary (out : DyadicBall) (left right : DyadicExpressionTrace)
  | exponential (child : DyadicExpressionTrace) (witness : DyadicExpTrace)
  deriving Repr

namespace DyadicExpressionTrace

def output : DyadicExpressionTrace → DyadicBall
  | .atom out => out
  | .unary out _ => out
  | .binary out _ _ => out
  | .exponential _ w => w.output

def check (cfg : BallConfig) (env : Nat → DyadicBall) : BallExpression → DyadicExpressionTrace → Bool
  | .const c, .atom out => decide (DyadicBall.ChecksPoint cfg.prec out c)
  | .input n, .atom out => decide (out.Coarsens (env n))
  | .pi, .atom out => decide ((out.toBall cfg.prec).coarsens ComplexBall.piBall)
  | .add a b, .binary out wa wb => check cfg env a wa && check cfg env b wb &&
      decide (DyadicBall.ChecksAdd out wa.output wb.output)
  | .neg a, .unary out wa => check cfg env a wa && decide (out.Coarsens wa.output.neg)
  | .mul a b, .binary out wa wb => check cfg env a wa && check cfg env b wb &&
      decide (DyadicBall.ChecksMul cfg.prec out wa.output wb.output)
  | .inv a, .unary out wa => check cfg env a wa && decide (DyadicBall.ChecksInv cfg.prec out wa.output)
  | .exp a, .exponential wa w => check cfg env a wa && w.check cfg wa.output
  | _, _ => false

end DyadicExpressionTrace

def threeDyadic (a b c : DyadicBall) : Nat → DyadicBall
  | 0 => a
  | 1 => b
  | 2 => c
  | _+3 => DyadicBall.zero

def thetaSeedTermExpression (j n : Nat) : BallExpression :=
  .mul
    (.mul (.mul (.rational ((if n%4<2 then 1 else -1)*(2*n+1 : Rat)^j)) (.input 0))
      (.div (.pow (.const ⟨0,1⟩) j) (.const ⟨0,2⟩)))
    (.sub (.input 1) (.mul (.rational ((-1 : Rat)^j)) (.input 2)))

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

def length : DyadicThetaLoop → Nat
  | .zero => 0
  | .step p _ _ => p.length+1

def state (prec : Nat) (bq bp bm : DyadicBall) : DyadicThetaLoop → DyadicThetaState
  | .zero => ⟨DyadicBall.zero, DyadicBall.one prec, bq, bp, bm⟩
  | .step _ _ s => s

def check (cfg : BallConfig) (j : Nat) (bq bp bm bp2 bm2 : DyadicBall) : DyadicThetaLoop → Bool
  | .zero => true
  | .step p term next =>
    let s := p.state cfg.prec bq bp bm
    p.check cfg j bq bp bm bp2 bm2 &&
    term.check cfg (threeDyadic s.coefficient s.positive s.negative)
      (thetaSeedTermExpression j p.length) &&
    decide (DyadicBall.ChecksAdd next.sum s.sum term.output) &&
    decide (DyadicBall.ChecksMul cfg.prec next.coefficient s.coefficient s.step) &&
    decide (DyadicBall.ChecksMul cfg.prec next.step s.step bq) &&
    decide (DyadicBall.ChecksMul cfg.prec next.positive s.positive bp2) &&
    decide (DyadicBall.ChecksMul cfg.prec next.negative s.negative bm2)

end DyadicThetaLoop

def thetaPositiveSeedExpression : BallExpression :=
  .exp (.mul (.input 0) .imaginaryUnit)

def thetaNegativeSeedExpression : BallExpression :=
  .exp (.mul (.neg (.input 0)) .imaginaryUnit)

structure DyadicThetaSeed where
  positive : DyadicExpressionTrace
  negative : DyadicExpressionTrace
  positiveSquare : DyadicBall
  negativeSquare : DyadicBall
  deriving Repr

namespace DyadicThetaSeed

def check (cfg : BallConfig) (bv : DyadicBall) (w : DyadicThetaSeed) : Bool :=
  w.positive.check cfg (threeDyadic bv .zero .zero) thetaPositiveSeedExpression &&
  w.negative.check cfg (threeDyadic bv .zero .zero) thetaNegativeSeedExpression &&
  decide (DyadicBall.ChecksMul cfg.prec w.positiveSquare w.positive.output w.positive.output) &&
  decide (DyadicBall.ChecksMul cfg.prec w.negativeSquare w.negative.output w.negative.output)

end DyadicThetaSeed

structure DyadicThetaTrace where
  loop : DyadicThetaLoop
  output : DyadicBall
  deriving Repr

namespace DyadicThetaTrace

def check (cfg : BallConfig) (j N err : Nat) (bq : DyadicBall) (seed : DyadicThetaSeed)
    (w : DyadicThetaTrace) : Bool :=
  decide (w.loop.length = N) &&
  w.loop.check cfg j bq seed.positive.output seed.negative.output
    seed.positiveSquare seed.negativeSquare &&
  decide (w.output.Coarsens ((w.loop.state cfg.prec bq seed.positive.output seed.negative.output).sum.inflate err))

end DyadicThetaTrace

def fiveDyadic (a b c d e : DyadicBall) : Nat → DyadicBall
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | _+5 => .zero

def thetaArgumentExpression : BallExpression :=
  .mul (.mul .pi (.input 0)) (.rational (1/2))

def thetaShiftedArgumentExpression : BallExpression :=
  .mul (.mul .pi (.sub (.input 0) (.input 1))) (.rational (1/2))

def thetaAFromJetsExpression : BallExpression :=
  .mul (.mul (.input 1) (.pow (.div (.input 2) (.input 3)) 2))
    (.exp (.mul (.mul (.sub (.input 0) (.rational 1)) .pi)
      (.div (.input 4) (.input 3))))

structure DyadicThetaATrace where
  argument : DyadicExpressionTrace
  shiftedArgument : DyadicExpressionTrace
  seed : DyadicThetaSeed
  shiftedSeed : DyadicThetaSeed
  theta0 : DyadicThetaTrace
  theta1 : DyadicThetaTrace
  thetaShifted : DyadicThetaTrace
  result : DyadicExpressionTrace
  deriving Repr

namespace DyadicThetaATrace

def output (w : DyadicThetaATrace) : DyadicBall := w.result.output

def check (cfg : BallConfig) (N err : Nat) (bq ba bc bz : DyadicBall)
    (w : DyadicThetaATrace) : Bool :=
  w.argument.check cfg (threeDyadic bz ba .zero) thetaArgumentExpression &&
  w.shiftedArgument.check cfg (threeDyadic bz ba .zero) thetaShiftedArgumentExpression &&
  decide (w.argument.output.ChecksImOne cfg.prec) &&
  decide (w.shiftedArgument.output.ChecksImOne cfg.prec) &&
  w.seed.check cfg w.argument.output && w.shiftedSeed.check cfg w.shiftedArgument.output &&
  w.theta0.check cfg 0 N err bq w.seed && w.theta1.check cfg 1 N err bq w.seed &&
  w.thetaShifted.check cfg 0 N err bq w.shiftedSeed && decide (0 < w.theta0.output.lower) &&
  w.result.check cfg (fiveDyadic ba bc w.thetaShifted.output w.theta0.output w.theta1.output)
    thetaAFromJetsExpression

end DyadicThetaATrace

structure DyadicCoefficientTrace where
  argument : DyadicExpressionTrace
  seedZero : DyadicThetaSeed
  seedA : DyadicThetaSeed
  thetaZero : DyadicThetaTrace
  thetaA : DyadicThetaTrace
  result : DyadicExpressionTrace
  deriving Repr

namespace DyadicCoefficientTrace

def output (w : DyadicCoefficientTrace) : DyadicBall := w.result.output

end DyadicCoefficientTrace

structure RangeDyadicParameters where
  height : DyadicBall
  abscissa : DyadicBall
  q : DyadicExpressionTrace
  coefficient : DyadicCoefficientTrace
  deriving Repr

structure RangeDerivativeParameters where
  base : RangeDyadicParameters
  thetaA1 : DyadicThetaTrace
  thetaA2 : DyadicThetaTrace
  thetaA3 : DyadicThetaTrace
  thetaA4 : DyadicThetaTrace
  thetaZero3 : DyadicThetaTrace
  ratioA : DyadicExpressionTrace
  ratioA2 : DyadicExpressionTrace
  ratioZero : DyadicExpressionTrace
  gt : DyadicExpressionTrace

structure RangeCertificateSetup where
  config : BallConfig
  terms : Nat
  error : Nat

def dyadicInputList (xs : List DyadicBall) (i : Nat) : DyadicBall := xs[i]?.getD .zero

def derivativeLaExpression : BallExpression :=
  .mul .pi (.sub (.sub (.div (.input 3) (.input 2)) (.div (.input 7) (.input 6))) (.input 9))

def derivativeLtExpression : BallExpression :=
  let rz := BallExpression.div (.input 3) (.input 2)
  let u2z := BallExpression.div (.input 4) (.input 2)
  let u3z := BallExpression.div (.input 5) (.input 2)
  let u2m := BallExpression.div (.input 8) (.input 6)
  .add (.mul (.mul .pi (.rational (1/4))) (.sub (.add (.sub (.input 11) (.input 10)) u2m) u2z))
    (.mul (.mul (.mul (.sub (.input 0) (.rational 1)) (.pow .pi 2)) (.rational (1/8)))
      (.sub u3z (.mul rz u2z)))

def derivativeLzExpression : BallExpression :=
  let rz := BallExpression.div (.input 3) (.input 2)
  let rm := BallExpression.div (.input 7) (.input 6)
  let u2z := BallExpression.div (.input 4) (.input 2)
  .add (.mul .pi (.sub rm rz))
    (.mul (.mul (.mul (.sub (.input 0) (.rational 1)) (.pow .pi 2)) (.rational (1/2)))
      (.sub u2z (.pow rz 2)))

def derivativeAaExpression : BallExpression := .mul (.input 1) derivativeLaExpression

def derivativeAtExpression : BallExpression := .mul (.input 1)
  (.add derivativeLtExpression (.mul (.const ⟨0,1/2⟩) derivativeLzExpression))

structure RangeDerivativeTrace where
  base : DyadicThetaATrace
  thetaZ2 : DyadicThetaTrace
  thetaZ3 : DyadicThetaTrace
  thetaM1 : DyadicThetaTrace
  thetaM2 : DyadicThetaTrace
  resultA : DyadicExpressionTrace
  resultT : DyadicExpressionTrace

namespace RangeDerivativeTrace

def inputs (p : RangeDerivativeParameters) (w : RangeDerivativeTrace) : List DyadicBall :=
  [p.base.abscissa,w.base.output,w.base.theta0.output,w.base.theta1.output,w.thetaZ2.output,
    w.thetaZ3.output,w.base.thetaShifted.output,w.thetaM1.output,w.thetaM2.output,
    p.ratioA.output,p.ratioA2.output,p.ratioZero.output]

def check (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (z : DyadicBall)
    (w : RangeDerivativeTrace) : Bool :=
  w.base.check s.config s.terms s.error p.base.q.output p.base.abscissa p.base.coefficient.output z &&
  w.thetaZ2.check s.config 2 s.terms s.error p.base.q.output w.base.seed &&
  w.thetaZ3.check s.config 3 s.terms s.error p.base.q.output w.base.seed &&
  w.thetaM1.check s.config 1 s.terms s.error p.base.q.output w.base.shiftedSeed &&
  w.thetaM2.check s.config 2 s.terms s.error p.base.q.output w.base.shiftedSeed &&
  decide (0 < w.base.thetaShifted.output.lower) &&
  w.resultA.check s.config (dyadicInputList (w.inputs p)) derivativeAaExpression &&
  w.resultT.check s.config (dyadicInputList (w.inputs p)) derivativeAtExpression

end RangeDerivativeTrace

structure RangeDerivativeNode where
  point : DyadicBall
  function : RangeDerivativeTrace
  weightedA : DyadicExpressionTrace
  weightedT : DyadicExpressionTrace

namespace RangeDerivativeNode

def check (s : RangeCertificateSetup) (p : RangeDerivativeParameters) (center : DyadicBall)
    (h node weight : Rat) (w : RangeDerivativeNode) : Bool :=
  decide ((w.point.toBall s.config.prec).coarsens
    (ComplexBall.add (center.toBall s.config.prec) (ComplexBall.rational (h*node)))) &&
  w.function.check s p w.point &&
  w.weightedA.check s.config (threeDyadic w.function.resultA.output .zero .zero)
    (.mul (.rational weight) (.input 0)) &&
  w.weightedT.check s.config (threeDyadic w.function.resultT.output .zero .zero)
    (.mul (.rational weight) (.input 0))

end RangeDerivativeNode

structure RangeDerivativeCell where
  center : DyadicBall
  disk : DyadicBall
  diskFunction : RangeDerivativeTrace
  nodes : Fin 12 → RangeDerivativeNode
  outputA : DyadicBall
  outputT : DyadicBall

end TwoAxisHelicoid.TraceData
