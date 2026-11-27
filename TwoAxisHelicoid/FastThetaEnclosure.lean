import TwoAxisHelicoid.FastThetaCore

namespace TwoAxisHelicoid
open ComplexBall

def evalThetaPartialFast (cfg : BallConfig) (j N : ℕ) (bt bv : ComplexBall) :
    Option ComplexBall := do
  let bq ← checkedExp cfg.prec cfg.terms cfg.squarings (neg (roundedMul cfg.prec piBall bt))
  let bp ← checkedExp cfg.prec cfg.terms cfg.squarings (roundedMul cfg.prec bv imaginaryBall)
  let bm ← checkedExp cfg.prec cfg.terms cfg.squarings (neg (roundedMul cfg.prec bv imaginaryBall))
  pure (fastThetaLoop cfg.prec j bq (roundedMul cfg.prec bp bp) (roundedMul cfg.prec bm bm)
    N 0 (rational 1) bq bp bm)

theorem evalThetaPartialFast_sound {bt bv : ComplexBall} {t : ℝ} {v : ℂ}
    (ht : bt.Contains (t : ℂ)) (hv : bv.Contains v) (cfg : BallConfig) (j N : ℕ) :
    Sound (evalThetaPartialFast cfg j N bt bv) (thetaPartial t j N v) := by
  unfold evalThetaPartialFast
  apply bind_sound (checkedExp_sound
    (neg_contains (roundedMul_contains piBall_contains ht cfg.prec)) cfg.prec cfg.terms cfg.squarings)
  intro bq hq
  apply bind_sound (checkedExp_sound (roundedMul_contains hv imaginaryBall_contains cfg.prec)
    cfg.prec cfg.terms cfg.squarings)
  intro bp hp
  apply bind_sound (checkedExp_sound (neg_contains (roundedMul_contains hv imaginaryBall_contains cfg.prec))
    cfg.prec cfg.terms cfg.squarings)
  intro bm hm
  have hp2 : (roundedMul cfg.prec bp bp).Contains (Complex.exp (2*v*Complex.I)) := by
    convert roundedMul_contains hp hp cfg.prec using 1
    rw [← Complex.exp_add]
    congr 1
    ring
  have hm2 : (roundedMul cfg.prec bm bm).Contains (Complex.exp (-2*v*Complex.I)) := by
    convert roundedMul_contains hm hm cfg.prec using 1
    rw [← Complex.exp_add]
    congr 1
    ring
  apply sound_some
  have hh := fastThetaLoop_contains cfg.prec j (t := t) (v := v)
    (by simpa only [neg_mul] using hq) hp2 hm2 N 0 (rational 1) bq bp bm
    (by simpa using rational_contains 1) (by simpa [neg_mul] using hq)
    (by simpa using hp) (by simpa using hm)
  simpa only [Nat.zero_add, thetaPartial] using hh

def evalThetaFast (cfg : BallConfig) (j N : ℕ) (bt bv : ComplexBall) : Option ComplexBall :=
  let tlo := bt.center.re-bt.radius
  let y := |bv.center.im|+bv.radius
  if 0 < tlo then do
    let b ← evalThetaPartialFast cfg j N bt bv
    let r ← evalThetaTail cfg tlo y j N
    pure (ComplexBall.round cfg.prec ⟨b.center, b.radius+r⟩)
  else none

theorem evalThetaFast_sound {bt bv : ComplexBall} {t : ℝ} {v : ℂ}
    (ht : bt.Contains (t : ℂ)) (hv : bv.Contains v) (cfg : BallConfig) (j N : ℕ) :
    Sound (evalThetaFast cfg j N bt bv) (thetaJet t j v) := by
  have hp := evalThetaPartialFast_sound ht hv cfg j N
  have htl := (ComplexBall.re_bounds ht).1
  simp only [Complex.ofReal_re] at htl
  have hvi := ComplexBall.abs_im_le hv
  unfold evalThetaFast
  dsimp only
  split_ifs with hg
  · have htlo : (0 : ℝ) < ((bt.center.re-bt.radius : ℚ) : ℝ) := by exact_mod_cast hg
    cases hb : evalThetaPartialFast cfg j N bt bv with
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

#print axioms TwoAxisHelicoid.evalThetaFast_sound
