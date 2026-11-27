import TwoAxisHelicoid.ThetaEnclosure
import TwoAxisHelicoid.ThetaPeriod

/-! A checked disk enclosure for the actual theta vertical-period equation. -/

namespace TwoAxisHelicoid
open ComplexBall

def verticalArgumentBall (cfg : BallConfig) (ba : ComplexBall) : ComplexBall :=
  roundedMul cfg.prec (roundedMul cfg.prec piBall ba) (ComplexBall.rational (1/2))

theorem verticalArgumentBall_contains {ba : ComplexBall} {a : ℝ} (ha : ba.Contains (a : ℂ))
    (cfg : BallConfig) : (verticalArgumentBall cfg ba).Contains (Real.pi*a/2 : ℂ) := by
  have hh := roundedMul_contains (roundedMul_contains piBall_contains ha cfg.prec)
    (rational_contains (1/2)) cfg.prec
  convert hh using 1
  · rfl
  · push_cast
    ring

def evalThetaG (cfg : BallConfig) (N : ℕ) (bt ba : ComplexBall) : Option ComplexBall := do
  let bv := verticalArgumentBall cfg ba
  let s0 ← evalTheta cfg 0 N bt bv
  let s1 ← evalTheta cfg 1 N bt bv
  let s2 ← evalTheta cfg 2 N bt bv
  let is0 ← checkedInv cfg.prec s0
  let it ← checkedInv cfg.prec bt
  let r := roundedMul cfg.prec s1 is0
  let u2 := roundedMul cfg.prec s2 is0
  let c := roundedMul cfg.prec (roundedMul cfg.prec piBall piBall) (ComplexBall.rational (1/4))
  pure (roundedAdd cfg.prec
    (roundedMul cfg.prec c (roundedAdd cfg.prec (roundedMul cfg.prec r r) (neg u2)))
    (neg (roundedMul cfg.prec piBall it)))

theorem evalThetaG_sound {bt ba : ComplexBall} {t a : ℝ}
    (ht : bt.Contains (t : ℂ)) (ha : ba.Contains (a : ℂ)) (cfg : BallConfig) (N : ℕ) :
    Sound (evalThetaG cfg N bt ba) (thetaG t a) := by
  have hv := verticalArgumentBall_contains ha cfg
  unfold evalThetaG
  apply bind_sound (evalTheta_sound ht hv cfg 0 N)
  intro s0 hs0
  apply bind_sound (evalTheta_sound ht hv cfg 1 N)
  intro s1 hs1
  apply bind_sound (evalTheta_sound ht hv cfg 2 N)
  intro s2 hs2
  apply bind_sound (checkedInv_sound hs0 cfg.prec)
  intro is0 his0
  apply bind_sound (checkedInv_sound ht cfg.prec)
  intro it hit
  have hr := roundedMul_contains hs1 his0 cfg.prec
  have hu := roundedMul_contains hs2 his0 cfg.prec
  have hc := roundedMul_contains (roundedMul_contains piBall_contains piBall_contains cfg.prec)
    (rational_contains (1/4)) cfg.prec
  have hpi := roundedMul_contains piBall_contains hit cfg.prec
  apply sound_some
  have hb := roundedAdd_contains
    (roundedMul_contains hc (roundedAdd_contains (roundedMul_contains hr hr cfg.prec)
      (neg_contains hu) cfg.prec) cfg.prec) (neg_contains hpi) cfg.prec
  convert hb using 1
  unfold thetaG thetaQuotient
  push_cast
  ring

def certifiesVerticalBounds (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi lo hi : ℚ) : Prop :=
  match evalThetaG cfg N (realInterval tlo thi) (realInterval alo ahi) with
  | none => False
  | some b => lo ≤ b.center.re-b.radius ∧ b.center.re+b.radius ≤ hi

instance (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi lo hi : ℚ) :
    Decidable (certifiesVerticalBounds cfg N tlo thi alo ahi lo hi) := by
  unfold certifiesVerticalBounds
  split <;> infer_instance

theorem certified_vertical_bounds (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi lo hi : ℚ)
    (hc : certifiesVerticalBounds cfg N tlo thi alo ahi lo hi) {t a : ℝ}
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    (lo : ℝ) ≤ (thetaG t a).re ∧ (thetaG t a).re ≤ (hi : ℝ) := by
  have hs := evalThetaG_sound (realInterval_contains htl htu) (realInterval_contains hal hau) cfg N
  unfold certifiesVerticalBounds at hc
  cases he : evalThetaG cfg N (realInterval tlo thi) (realInterval alo ahi) with
  | none => simp only [he] at hc
  | some b =>
    simp only [he] at hc
    have hb := re_bounds (hs b he)
    exact ⟨(Rat.cast_le.mpr hc.1).trans hb.1, hb.2.trans (Rat.cast_le.mpr hc.2)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certified_vertical_bounds
