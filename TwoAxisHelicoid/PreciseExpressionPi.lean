import TwoAxisHelicoid.DyadicExpressionTrace

namespace TwoAxisHelicoid

/-- Supply the π disk as an ordinary checked input and shift all
pre-existing input indices by one. -/
def BallExpression.withPiInput : BallExpression → BallExpression
  | .input n => .input (n+1)
  | .pi => .input 0
  | .const c => .const c
  | .add a b => .add a.withPiInput b.withPiInput
  | .neg a => .neg a.withPiInput
  | .mul a b => .mul a.withPiInput b.withPiInput
  | .inv a => .inv a.withPiInput
  | .exp a => .exp a.withPiInput

def piInputEnvironment {α : Type*} (p : α) (e : ℕ → α) : ℕ → α
  | 0 => p
  | n+1 => e n

theorem BallExpression.value_withPiInput (e : BallExpression) (env : ℕ → ℂ) :
    e.withPiInput.value (piInputEnvironment (Real.pi:ℂ) env)=e.value env := by
  induction e <;> simp_all only [BallExpression.withPiInput,BallExpression.value,piInputEnvironment]

abbrev DyadicExpressionTrace.WithPi (w : DyadicExpressionTrace) (cfg : BallConfig)
    (p : DyadicBall) (env : ℕ → DyadicBall) (e : BallExpression) :=
  w.Valid cfg (piInputEnvironment p env) e.withPiInput

theorem DyadicExpressionTrace.withPi_sound (w : DyadicExpressionTrace) (cfg : BallConfig)
    {bp : DyadicBall} (piOk : (bp.toBall cfg.prec).Contains (Real.pi:ℂ))
    (env : ℕ → DyadicBall) (values : ℕ → ℂ) (he : ∀ n, ((env n).toBall cfg.prec).Contains (values n))
    (e : BallExpression) (check : w.WithPi cfg bp env e) :
    (w.output.toBall cfg.prec).Contains (e.value values) := by
  have allInputs (n : ℕ) : ((piInputEnvironment bp env n).toBall cfg.prec).Contains
      (piInputEnvironment (Real.pi:ℂ) values n) := by
    cases n with
    | zero => exact piOk
    | succ n => exact he n
  simpa only [BallExpression.value_withPiInput] using w.sound cfg _ _ allInputs _ check

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.DyadicExpressionTrace.withPi_sound
