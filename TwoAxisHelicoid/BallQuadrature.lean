import TwoAxisHelicoid.HorizontalEnclosure
import TwoAxisHelicoid.QuadratureRule

namespace TwoAxisHelicoid
open ComplexBall

def evalFinSum (prec : ℕ) : (K : ℕ) → (Fin K → Option ComplexBall) → Option ComplexBall
  | 0, _ => some (rational 0)
  | K+1, f => mapTwo (roundedAdd prec) (f 0) (evalFinSum prec K (fun i => f i.succ))

theorem evalFinSum_sound (prec K : ℕ) (f : Fin K → Option ComplexBall) (v : Fin K → ℂ)
    (hf : ∀ i, Sound (f i) (v i)) : Sound (evalFinSum prec K f) (∑ i, v i) := by
  induction K with
  | zero =>
    apply sound_some
    simpa using rational_contains 0
  | succ K ih =>
    rw [Fin.sum_univ_succ]
    exact mapTwo_sound (hf 0) (ih (fun i => f i.succ) (fun i => v i.succ) (fun i => hf i.succ))
      _ (fun _ _ h₁ h₂ => roundedAdd_contains h₁ h₂ prec)

def evalThetaQuadrature {K : ℕ} (cfg : BallConfig) (N : ℕ) (q : QuadratureRule K)
    (bt ba bc center : ComplexBall) (h : ℚ) : Option ComplexBall :=
  evalFinSum cfg.prec K (fun i => do
    let b ← evalThetaAWithCoefficient cfg N bt ba bc
      (roundedAdd cfg.prec center (rational (h*q.node i)))
    pure (roundedMul cfg.prec (rational (q.weight i)) b))

theorem evalThetaQuadrature_sound {K : ℕ} {bt ba bc center : ComplexBall} {t a : ℝ} {c : ℂ}
    (ht : bt.Contains (t : ℂ)) (ha : ba.Contains (a : ℂ))
    (hc : bc.Contains (thetaACoefficient t a)) (hcenter : center.Contains c)
    (cfg : BallConfig) (N : ℕ) (q : QuadratureRule K) (h : ℚ) :
    Sound (evalThetaQuadrature cfg N q bt ba bc center h) (q.apply (thetaA t a) c (h : ℝ)) := by
  unfold evalThetaQuadrature QuadratureRule.apply
  apply evalFinSum_sound
  intro i
  have hp : (roundedAdd cfg.prec center (rational (h*q.node i))).Contains
      (c+((h : ℝ) : ℂ)*(q.node i : ℂ)) := by
    simpa only [Rat.cast_mul, Complex.ofReal_ratCast] using
      roundedAdd_contains hcenter (rational_contains (h*q.node i)) cfg.prec
  apply bind_sound (evalThetaAWithCoefficient_sound ht ha hc hp cfg N)
  intro b hb
  exact sound_some (roundedMul_contains (rational_contains (q.weight i)) hb cfg.prec)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.evalThetaQuadrature_sound
