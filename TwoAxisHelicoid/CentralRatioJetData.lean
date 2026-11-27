import TwoAxisHelicoid.CentralBandEdgeData
import TwoAxisHelicoid.CentralRatioSlopeParameter

namespace TwoAxisHelicoid

def jetCons {α : Type} (value : α) (previous : ℕ → α) : ℕ → α
  | 0 => value
  | n+1 => previous n

def jetProgramChecks (cfg : BallConfig) : (ℕ → DyadicBall) → List BallExpression → List DyadicExpressionTrace → Prop
  | _, [], [] => True
  | env, e::es, w::ws => w.Valid cfg env e ∧ jetProgramChecks cfg (jetCons w.output env) es ws
  | _, [], _::_ | _, _::_, [] => False

instance jetProgramDecidable (cfg : BallConfig) (env : ℕ → DyadicBall) (es : List BallExpression) (ws : List DyadicExpressionTrace) :
    Decidable (jetProgramChecks cfg env es ws) :=
  match es,ws with
  | [],[] => isTrue True.intro
  | [],_::_ | _::_,[] => isFalse id
  | e::es,w::ws => by
    haveI := jetProgramDecidable cfg (jetCons w.output env) es ws
    change Decidable (w.Valid cfg env e ∧ _)
    infer_instance

def jetProgramOutput : DyadicBall → List DyadicExpressionTrace → DyadicBall
  | b, [] => b
  | _, w::ws => jetProgramOutput w.output ws

noncomputable def jetProgramValue : (ℕ → ℂ) → List BallExpression → ℂ
  | env, [] => env 0
  | env, e::es => jetProgramValue (jetCons (e.value env) env) es

theorem jet_program_sound {cfg : BallConfig} {env : ℕ → DyadicBall} {v : ℕ → ℂ} {es : List BallExpression}
    {ws : List DyadicExpressionTrace} (inputs : ∀ i, ((env i).toBall cfg.prec).Contains (v i))
    (check : jetProgramChecks cfg env es ws) :
    ((jetProgramOutput (env 0) ws).toBall cfg.prec).Contains (jetProgramValue v es) := by
  induction es generalizing env v ws with
  | nil =>
    cases ws with
    | nil => exact inputs 0
    | cons w ws => exact False.elim check
  | cons e es ih =>
    cases ws with
    | nil => exact False.elim check
    | cons w ws =>
      apply ih (env:=jetCons w.output env) (v:=jetCons (e.value v) v) (ws:=ws) _ check.2
      intro i
      cases i with
      | zero => exact w.sound _ _ _ inputs _ check.1
      | succ n => exact inputs n

def centralRatioJetStep (j : ℕ) : BallExpression :=
  let c := BallExpression.input j
  let e := BallExpression.input (j+1)
  let m := fun k => BallExpression.input (j+2+k)
  let p := fun k => BallExpression.input (j+6+k)
  let n := BallExpression.rational
  let sub := BallExpression.sub
  let add := BallExpression.add
  let mul := BallExpression.mul
  let pw := BallExpression.pow
  let numerator := match j with
    | 0 => mul e (m 0)
    | 1 => sub (mul e (add (mul c (m 0)) (m 1))) (mul (.input 0) (p 1))
    | 2 => sub (sub (mul e (add (add (mul (pw c 2) (m 0)) (mul (mul (n 2) c) (m 1))) (m 2)))
        (mul (.input 1) (p 2))) (mul (mul (n 2) (.input 0)) (p 1))
    | _ => sub (sub (sub (mul e (add (add (add (mul (pw c 3) (m 0)) (mul (mul (n 3) (pw c 2)) (m 1)))
        (mul (mul (n 3) c) (m 2))) (m 3))) (mul (.input 2) (p 3))) (mul (mul (n 3) (.input 1)) (p 2)))
        (mul (mul (n 3) (.input 0)) (p 1))
  .div numerator (p 0)

def centralRatioProgram (third : Bool) : List BallExpression :=
  if third then [centralRatioJetStep 0,centralRatioJetStep 1,centralRatioJetStep 2,centralRatioJetStep 3]
  else [centralRatioJetStep 0,centralRatioJetStep 1,centralRatioJetStep 2]

def centralRatioInputs {α : Type} (c e : α) (minus plus : ℕ → α) : ℕ → α
  | 0 => c | 1 => e | 2 => minus 0 | 3 => minus 1 | 4 => minus 2 | 5 => minus 3
  | 6 => plus 0 | 7 => plus 1 | 8 => plus 2 | 9 => plus 3 | _+10 => c

def centralRatioExpExpression : BallExpression := .exp (.mul (.mul (.mul .pi (.rational (1/2))) (.input 0)) (.input 1))

def centralShiftExpression (plus : Bool) : BallExpression :=
  .mul (.mul .pi (if plus then .add (.input 0) (.input 1) else .sub (.input 0) (.input 1))) (.rational (1/2))

structure CentralShiftJets where
  argument : DyadicExpressionTrace
  seed : DyadicThetaSeed
  j0 : DyadicThetaTrace
  j1 : DyadicThetaTrace
  j2 : DyadicThetaTrace
  j3 : Option DyadicThetaTrace

def CentralShiftJets.output (w : CentralShiftJets) : ℕ → DyadicBall
  | 0 => w.j0.output | 1 => w.j1.output | 2 => w.j2.output
  | 3 => (w.j3.map DyadicThetaTrace.output).getD .zero
  | _+4 => .zero

def optionalThirdCheck (cfg : BallConfig) (n err : ℕ) (q : DyadicBall) (seed : DyadicThetaSeed) :
    Bool → Option DyadicThetaTrace → Prop
  | false, none => True
  | true, some w => w.Valid cfg 3 n err q seed
  | _,_ => False

instance optionalThirdCheckDecidable (cfg : BallConfig) (n err : ℕ) (q : DyadicBall) (s : DyadicThetaSeed) (high : Bool) (w : Option DyadicThetaTrace) :
    Decidable (optionalThirdCheck cfg n err q s high w) := by
  cases high <;> cases w <;> unfold optionalThirdCheck <;> infer_instance

def CentralShiftJets.Checks (w : CentralShiftJets) (box : DyadicBall) (high plus : Bool) : Prop :=
  let S := slopingFluxAnalyticSetup
  let p := TraceData.slopingFluxParams
  let q := p.q.output.interpret
  w.argument.Valid S.config (threeDyadic box p.abscissa.interpret .zero) (centralShiftExpression plus) ∧
  w.argument.output.ChecksImOne S.config.prec ∧ w.seed.Valid S.config w.argument.output ∧
  w.j0.Valid S.config 0 S.terms S.error q w.seed ∧ w.j1.Valid S.config 1 S.terms S.error q w.seed ∧
  w.j2.Valid S.config 2 S.terms S.error q w.seed ∧ optionalThirdCheck S.config S.terms S.error q w.seed high w.j3

instance centralShiftJetsChecksDecidable (w : CentralShiftJets) (box : DyadicBall) (high plus : Bool) : Decidable (w.Checks box high plus) := by
  unfold CentralShiftJets.Checks
  infer_instance

structure CentralRatioJetTrace where
  box : DyadicBall
  exponential : DyadicExpressionTrace
  minus : CentralShiftJets
  plus : CentralShiftJets
  steps : List DyadicExpressionTrace

def CentralRatioJetTrace.Checks (w : CentralRatioJetTrace) (high vertical : Bool) (edge l r : ℚ) : Prop :=
  let S := slopingFluxAnalyticSetup
  let c := centralRatioSlopeTrace.output
  let out := (jetProgramOutput c w.steps).toBall S.config.prec
  (w.box.toBall S.config.prec).coarsens (centralBandEdgeBall vertical edge l r) ∧
  w.exponential.Valid S.config (threeDyadic c w.box .zero) centralRatioExpExpression ∧
  w.minus.Checks w.box high false ∧ w.plus.Checks w.box high true ∧
  jetProgramChecks S.config (centralRatioInputs c w.exponential.output w.minus.output w.plus.output) (centralRatioProgram high) w.steps ∧
  1/1024<out.center.re-out.radius

instance centralRatioJetChecksDecidable (w : CentralRatioJetTrace) (h v : Bool) (e l r : ℚ) : Decidable (w.Checks h v e l r) := by
  unfold CentralRatioJetTrace.Checks
  infer_instance

inductive CheckedCentralRatioJets : Bool → Bool → ℚ → ℚ → ℚ → Prop
  | leaf (w : CentralRatioJetTrace) {h v e l r} (ok : w.Checks h v e l r) : CheckedCentralRatioJets h v e l r
  | join {h v e l m r} : CheckedCentralRatioJets h v e l m → CheckedCentralRatioJets h v e m r → CheckedCentralRatioJets h v e l r

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.jet_program_sound
