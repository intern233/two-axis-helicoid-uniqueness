import TwoAxisHelicoid.VerticalEnclosure

namespace TwoAxisHelicoid
open ComplexBall

noncomputable def thetaGa (t a : ℝ) : ℂ :=
  (Real.pi^3/8 : ℂ) *
    (3*thetaQuotient t 1 (Real.pi*a/2)*thetaQuotient t 2 (Real.pi*a/2) -
      2*(thetaQuotient t 1 (Real.pi*a/2))^3 - thetaQuotient t 3 (Real.pi*a/2))

def evalThetaGa (cfg : BallConfig) (N : ℕ) (bt ba : ComplexBall) : Option ComplexBall := do
  let bv := verticalArgumentBall cfg ba
  let s0 ← evalTheta cfg 0 N bt bv
  let s1 ← evalTheta cfg 1 N bt bv
  let s2 ← evalTheta cfg 2 N bt bv
  let s3 ← evalTheta cfg 3 N bt bv
  let is0 ← checkedInv cfg.prec s0
  let r := roundedMul cfg.prec s1 is0
  let u2 := roundedMul cfg.prec s2 is0
  let u3 := roundedMul cfg.prec s3 is0
  let c := roundedMul cfg.prec
    (roundedMul cfg.prec (roundedMul cfg.prec piBall piBall) piBall) (ComplexBall.rational (1/8))
  pure (roundedMul cfg.prec c
    (roundedAdd cfg.prec
      (roundedAdd cfg.prec (roundedMul cfg.prec (roundedMul cfg.prec (ComplexBall.rational 3) r) u2)
        (neg (roundedMul cfg.prec (ComplexBall.rational 2) (roundedMul cfg.prec (roundedMul cfg.prec r r) r))))
      (neg u3)))

theorem evalThetaGa_sound {bt ba : ComplexBall} {t a : ℝ}
    (ht : bt.Contains (t : ℂ)) (ha : ba.Contains (a : ℂ)) (cfg : BallConfig) (N : ℕ) :
    Sound (evalThetaGa cfg N bt ba) (thetaGa t a) := by
  have hv := verticalArgumentBall_contains ha cfg
  unfold evalThetaGa
  apply bind_sound (evalTheta_sound ht hv cfg 0 N)
  intro s0 hs0
  apply bind_sound (evalTheta_sound ht hv cfg 1 N)
  intro s1 hs1
  apply bind_sound (evalTheta_sound ht hv cfg 2 N)
  intro s2 hs2
  apply bind_sound (evalTheta_sound ht hv cfg 3 N)
  intro s3 hs3
  apply bind_sound (checkedInv_sound hs0 cfg.prec)
  intro is0 his0
  have hr := roundedMul_contains hs1 his0 cfg.prec
  have hu2 := roundedMul_contains hs2 his0 cfg.prec
  have hu3 := roundedMul_contains hs3 his0 cfg.prec
  have hc := roundedMul_contains (roundedMul_contains
    (roundedMul_contains piBall_contains piBall_contains cfg.prec) piBall_contains cfg.prec)
    (rational_contains (1/8)) cfg.prec
  have hr3 := roundedMul_contains (roundedMul_contains hr hr cfg.prec) hr cfg.prec
  have hb := roundedMul_contains hc
    (roundedAdd_contains (roundedAdd_contains
      (roundedMul_contains (roundedMul_contains (rational_contains 3) hr cfg.prec) hu2 cfg.prec)
      (neg_contains (roundedMul_contains (rational_contains 2) hr3 cfg.prec)) cfg.prec)
      (neg_contains hu3) cfg.prec) cfg.prec
  apply sound_some
  convert hb using 1
  unfold thetaGa thetaQuotient
  push_cast
  ring

def certifiesVerticalDenominator (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi : ℚ) : Prop :=
  match evalTheta cfg 0 N (realInterval tlo thi) (verticalArgumentBall cfg (realInterval alo ahi)) with
  | none => False
  | some b => 0 < b.lower

instance (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi : ℚ) :
    Decidable (certifiesVerticalDenominator cfg N tlo thi alo ahi) := by
  unfold certifiesVerticalDenominator
  split <;> infer_instance

theorem certified_vertical_denominator (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi : ℚ)
    (hc : certifiesVerticalDenominator cfg N tlo thi alo ahi) {t a : ℝ}
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    thetaJet t 0 (Real.pi*a/2) ≠ 0 := by
  have hs := evalTheta_sound (realInterval_contains htl htu)
    (verticalArgumentBall_contains (realInterval_contains hal hau) cfg) cfg 0 N
  unfold certifiesVerticalDenominator at hc
  cases he : evalTheta cfg 0 N (realInterval tlo thi) (verticalArgumentBall cfg (realInterval alo ahi)) with
  | none => simp only [he] at hc
  | some b =>
    simp only [he] at hc
    exact ne_zero_of_lower_pos (hs b he) hc

def certifiesVerticalDerivativeUpper (cfg : BallConfig) (N : ℕ)
    (tlo thi alo ahi upper : ℚ) : Prop :=
  match evalThetaGa cfg N (realInterval tlo thi) (realInterval alo ahi) with
  | none => False
  | some b => b.center.re+b.radius ≤ upper

instance (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi upper : ℚ) :
    Decidable (certifiesVerticalDerivativeUpper cfg N tlo thi alo ahi upper) := by
  unfold certifiesVerticalDerivativeUpper
  split <;> infer_instance

theorem certified_vertical_derivative_upper (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi upper : ℚ)
    (hc : certifiesVerticalDerivativeUpper cfg N tlo thi alo ahi upper) {t a : ℝ}
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) : (thetaGa t a).re ≤ (upper : ℝ) := by
  have hs := evalThetaGa_sound (realInterval_contains htl htu) (realInterval_contains hal hau) cfg N
  unfold certifiesVerticalDerivativeUpper at hc
  cases he : evalThetaGa cfg N (realInterval tlo thi) (realInterval alo ahi) with
  | none => simp only [he] at hc
  | some b =>
    simp only [he] at hc
    exact (re_bounds (hs b he)).2.trans (Rat.cast_le.mpr hc)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certified_vertical_derivative_upper
