import TwoAxisHelicoid.ThetaExpression

/-! A fully proved evaluator for the actual infinite theta derivative series. -/

namespace TwoAxisHelicoid
open ComplexBall BallExpression

def zeroBallEnvironment : ℕ → ComplexBall := fun _ => ComplexBall.rational 0

def thetaBallEnvironment (bt bv : ComplexBall) : ℕ → ComplexBall
  | 0 => bt
  | 1 => bv
  | _+2 => ComplexBall.rational 0

def evalThetaTail (cfg : BallConfig) (tlo y : ℚ) (j N : ℕ) : Option ℚ :=
  match BallExpression.eval cfg zeroBallEnvironment (thetaMajorantExpression tlo y j N),
    BallExpression.eval cfg zeroBallEnvironment (thetaRatioExpression tlo y j N) with
  | some b, some r =>
    let bu := b.center.re+b.radius
    let ru := r.center.re+r.radius
    if ru < 1 then some (bu/(1-ru)) else none
  | _, _ => none

theorem evalThetaTail_sound (cfg : BallConfig) (tlo y : ℚ) (j N : ℕ) {r : ℚ}
    (h : evalThetaTail cfg tlo y j N = some r) :
    thetaRatio tlo y j N < 1 ∧
      thetaMajorant tlo y j N / (1-thetaRatio tlo y j N) ≤ (r : ℝ) := by
  have he : ∀ n, (zeroBallEnvironment n).Contains (0 : ℂ) :=
    fun _ => by simpa only [zeroBallEnvironment, Rat.cast_zero] using rational_contains 0
  have hB := BallExpression.eval_sound cfg zeroBallEnvironment (fun _ => 0) he
    (thetaMajorantExpression tlo y j N)
  have hR := BallExpression.eval_sound cfg zeroBallEnvironment (fun _ => 0) he
    (thetaRatioExpression tlo y j N)
  rw [value_thetaMajorantExpression] at hB
  rw [value_thetaRatioExpression] at hR
  cases hb : BallExpression.eval cfg zeroBallEnvironment (thetaMajorantExpression tlo y j N) with
  | none => simp [evalThetaTail, hb] at h
  | some b =>
    cases hr : BallExpression.eval cfg zeroBallEnvironment (thetaRatioExpression tlo y j N) with
    | none => simp [evalThetaTail, hb, hr] at h
    | some rr =>
      simp only [evalThetaTail, hb, hr] at h
      split_ifs at h with hg
      · cases Option.some.inj h
        have hbb := (ComplexBall.re_bounds (hB b hb)).2
        have hrr := (ComplexBall.re_bounds (hR rr hr)).2
        simp only [Complex.ofReal_re] at hbb hrr
        have hgu : ((rr.center.re+rr.radius : ℚ) : ℝ) < 1 := by exact_mod_cast hg
        have hrho : thetaRatio tlo y j N < 1 := hrr.trans_lt hgu
        refine ⟨hrho, ?_⟩
        rw [Rat.cast_div, Rat.cast_sub, Rat.cast_one]
        calc
          _ ≤ ((b.center.re+b.radius : ℚ) : ℝ)/(1-thetaRatio tlo y j N) :=
            div_le_div_of_nonneg_right hbb (by linarith)
          _ ≤ _ := div_le_div_of_nonneg_left
            ((thetaMajorant_nonneg _ _ _ _).trans hbb) (by linarith) (by linarith)

def evalTheta (cfg : BallConfig) (j N : ℕ) (bt bv : ComplexBall) : Option ComplexBall :=
  let tlo := bt.center.re-bt.radius
  let y := |bv.center.im|+bv.radius
  if 0 < tlo then do
    let b ← BallExpression.eval cfg (thetaBallEnvironment bt bv) (thetaPartialExpression j N)
    let r ← evalThetaTail cfg tlo y j N
    pure (ComplexBall.round cfg.prec ⟨b.center, b.radius+r⟩)
  else none

theorem evalTheta_sound {bt bv : ComplexBall} {t : ℝ} {v : ℂ}
    (ht : bt.Contains (t : ℂ)) (hv : bv.Contains v) (cfg : BallConfig) (j N : ℕ) :
    Sound (evalTheta cfg j N bt bv) (thetaJet t j v) := by
  have he : ∀ n, (thetaBallEnvironment bt bv n).Contains (thetaValues t v n) := by
    intro n
    rcases n with _ | (_ | n)
    · exact ht
    · exact hv
    · simpa only [thetaBallEnvironment, thetaValues, Rat.cast_zero] using rational_contains 0
  have hp := BallExpression.eval_sound cfg (thetaBallEnvironment bt bv) (thetaValues t v) he
    (thetaPartialExpression j N)
  rw [value_thetaPartialExpression] at hp
  have htl := (ComplexBall.re_bounds ht).1
  simp only [Complex.ofReal_re] at htl
  have hvi := ComplexBall.abs_im_le hv
  unfold evalTheta
  dsimp only
  split_ifs with hg
  · have htlo : (0 : ℝ) < ((bt.center.re-bt.radius : ℚ) : ℝ) := by exact_mod_cast hg
    cases hb : BallExpression.eval cfg (thetaBallEnvironment bt bv) (thetaPartialExpression j N) with
    | none => simp [Sound]
    | some b =>
      cases hr : evalThetaTail cfg (bt.center.re-bt.radius) (|bv.center.im|+bv.radius) j N with
      | none => simp [Sound]
      | some r =>
        apply sound_some
        apply ComplexBall.round_contains
        have htail := evalThetaTail_sound cfg (bt.center.re-bt.radius) (|bv.center.im|+bv.radius) j N hr
        have hbnd := (thetaJet_tail_bound htlo htl hvi j N htail.1).trans htail.2
        have hpval := hp b hb
        unfold Contains at *
        dsimp
        push_cast
        have hn := norm_add_le (thetaJet t j v-thetaPartial t j N v)
          (thetaPartial t j N v-b.center.val)
        rw [sub_add_sub_cancel] at hn
        change ‖thetaJet t j v-thetaPartial t j N v‖ ≤ (r : ℝ) at hbnd
        linarith
  · simp [Sound]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.evalTheta_sound
