import TwoAxisHelicoid.ComplexBallChecked

/-! A compositional checker for complex arithmetic expressions and their rational enclosures. -/

namespace TwoAxisHelicoid
namespace ComplexBall

theorem bind_sound {b : Option ComplexBall} {z w : ℂ} (hb : Sound b z)
    (f : ComplexBall → Option ComplexBall)
    (hf : ∀ a, a.Contains z → Sound (f a) w) : Sound (b.bind f) w := by
  cases b with
  | none => simp [Sound]
  | some a => exact hf a (hb a rfl)

end ComplexBall

structure BallConfig where
  prec : ℕ := 112
  terms : ℕ := 24
  squarings : ℕ := 16
  deriving DecidableEq, Repr

inductive BallExpression where
  | const (c : QComplex)
  | input (n : ℕ)
  | pi
  | add (a b : BallExpression)
  | neg (a : BallExpression)
  | mul (a b : BallExpression)
  | inv (a : BallExpression)
  | exp (a : BallExpression)
  deriving DecidableEq, Repr

namespace BallExpression
open ComplexBall

def rational (q : ℚ) : BallExpression := .const (QComplex.ofRat q)
def sub (a b : BallExpression) : BallExpression := .add a (.neg b)
def div (a b : BallExpression) : BallExpression := .mul a (.inv b)
def pow (a : BallExpression) : ℕ → BallExpression
  | 0 => rational 1
  | n+1 => .mul (pow a n) a

noncomputable def value (env : ℕ → ℂ) : BallExpression → ℂ
  | .const c => c.val
  | .input n => env n
  | .pi => Real.pi
  | .add a b => value env a + value env b
  | .neg a => -value env a
  | .mul a b => value env a * value env b
  | .inv a => (value env a)⁻¹
  | .exp a => Complex.exp (value env a)

@[simp] theorem value_rational (env : ℕ → ℂ) (q : ℚ) : value env (rational q) = (q : ℂ) := by
  simp [rational, value]

@[simp] theorem value_sub (env : ℕ → ℂ) (a b : BallExpression) :
    value env (sub a b) = value env a-value env b := by simp [sub, value, sub_eq_add_neg]

@[simp] theorem value_div (env : ℕ → ℂ) (a b : BallExpression) :
    value env (div a b) = value env a/value env b := by simp [div, value, div_eq_mul_inv]

@[simp] theorem value_pow (env : ℕ → ℂ) (a : BallExpression) (n : ℕ) :
    value env (pow a n) = (value env a)^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, value, ih, pow_succ]

def eval (cfg : BallConfig) (env : ℕ → ComplexBall) : BallExpression → Option ComplexBall
  | .const c => some (point c)
  | .input n => some (env n)
  | .pi => some piBall
  | .add a b => mapTwo (roundedAdd cfg.prec) (eval cfg env a) (eval cfg env b)
  | .neg a => (eval cfg env a).bind (fun b => some (ComplexBall.neg b))
  | .mul a b => mapTwo (roundedMul cfg.prec) (eval cfg env a) (eval cfg env b)
  | .inv a => (eval cfg env a).bind (checkedInv cfg.prec)
  | .exp a => (eval cfg env a).bind (checkedExp cfg.prec cfg.terms cfg.squarings)

theorem eval_sound (cfg : BallConfig) (env : ℕ → ComplexBall) (values : ℕ → ℂ)
    (hvalues : ∀ n, (env n).Contains (values n)) (e : BallExpression) :
    Sound (eval cfg env e) (value values e) := by
  induction e with
  | const c => exact sound_some (point_contains c)
  | input n => exact sound_some (hvalues n)
  | pi => exact sound_some piBall_contains
  | add a b ha hb =>
    exact mapTwo_sound ha hb _ (fun _ _ h₁ h₂ => roundedAdd_contains h₁ h₂ cfg.prec)
  | neg a ha => exact bind_sound ha _ (fun _ h => sound_some (neg_contains h))
  | mul a b ha hb =>
    exact mapTwo_sound ha hb _ (fun _ _ h₁ h₂ => roundedMul_contains h₁ h₂ cfg.prec)
  | inv a ha => exact bind_sound ha _ (fun _ h => checkedInv_sound h cfg.prec)
  | exp a ha =>
    exact bind_sound ha _ (fun _ h => checkedExp_sound h cfg.prec cfg.terms cfg.squarings)

def certifiesRealBounds (cfg : BallConfig) (env : ℕ → ComplexBall)
    (e : BallExpression) (lo hi : ℚ) : Prop :=
  match eval cfg env e with
  | none => False
  | some b => lo ≤ b.center.re-b.radius ∧ b.center.re+b.radius ≤ hi

instance (cfg : BallConfig) (env : ℕ → ComplexBall) (e : BallExpression) (lo hi : ℚ) :
    Decidable (certifiesRealBounds cfg env e lo hi) := by
  unfold certifiesRealBounds
  split <;> infer_instance

theorem certified_real_bounds (cfg : BallConfig) (env : ℕ → ComplexBall) (values : ℕ → ℂ)
    (hvalues : ∀ n, (env n).Contains (values n)) (e : BallExpression) (lo hi : ℚ)
    (hc : certifiesRealBounds cfg env e lo hi) :
    (lo : ℝ) ≤ (value values e).re ∧ (value values e).re ≤ (hi : ℝ) := by
  have hs := eval_sound cfg env values hvalues e
  unfold certifiesRealBounds at hc
  cases he : eval cfg env e with
  | none => simp only [he] at hc
  | some b =>
    simp only [he] at hc
    have hb := re_bounds (hs b he)
    constructor
    · exact (Rat.cast_le.mpr hc.1).trans hb.1
    · exact hb.2.trans (Rat.cast_le.mpr hc.2)

end BallExpression
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.BallExpression.certified_real_bounds
