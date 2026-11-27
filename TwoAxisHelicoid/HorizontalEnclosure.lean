import TwoAxisHelicoid.FastThetaEnclosure
import TwoAxisHelicoid.VerticalEnclosure
import TwoAxisHelicoid.ThetaPeriodIntegral

namespace TwoAxisHelicoid
open ComplexBall

noncomputable def thetaACoefficient (t a : ℝ) : ℂ :=
  ((Real.pi*thetaJet t 1 0)/(2*thetaJet t 0 (Real.pi*a/2)))^2

def complexArgumentBall (cfg : BallConfig) (bz : ComplexBall) : ComplexBall :=
  roundedMul cfg.prec (roundedMul cfg.prec piBall bz) (rational (1/2))

theorem complexArgumentBall_contains {bz : ComplexBall} {z : ℂ}
    (hz : bz.Contains z) (cfg : BallConfig) :
    (complexArgumentBall cfg bz).Contains (Real.pi*z/2) := by
  convert roundedMul_contains (roundedMul_contains piBall_contains hz cfg.prec)
    (rational_contains (1/2)) cfg.prec using 1
  · rfl
  · push_cast
    ring

def evalThetaACoefficient (cfg : BallConfig) (N : ℕ) (bt ba : ComplexBall) :
    Option ComplexBall := do
  let s1 ← evalThetaFast cfg 1 N bt (rational 0)
  let sa ← evalThetaFast cfg 0 N bt (verticalArgumentBall cfg ba)
  let isa ← checkedInv cfg.prec sa
  let b := roundedMul cfg.prec
    (roundedMul cfg.prec (roundedMul cfg.prec piBall s1) (rational (1/2))) isa
  pure (roundedMul cfg.prec b b)

theorem evalThetaACoefficient_sound {bt ba : ComplexBall} {t a : ℝ}
    (ht : bt.Contains (t : ℂ)) (ha : ba.Contains (a : ℂ)) (cfg : BallConfig) (N : ℕ) :
    Sound (evalThetaACoefficient cfg N bt ba) (thetaACoefficient t a) := by
  have hz : (rational 0).Contains (0 : ℂ) := by simpa using rational_contains 0
  unfold evalThetaACoefficient
  apply bind_sound (evalThetaFast_sound ht hz cfg 1 N)
  intro s1 hs1
  apply bind_sound (evalThetaFast_sound ht (verticalArgumentBall_contains ha cfg) cfg 0 N)
  intro sa hsa
  apply bind_sound (checkedInv_sound hsa cfg.prec)
  intro isa hisa
  have hb := roundedMul_contains (roundedMul_contains
    (roundedMul_contains piBall_contains hs1 cfg.prec) (rational_contains (1/2)) cfg.prec)
    hisa cfg.prec
  apply sound_some
  convert roundedMul_contains hb hb cfg.prec using 1
  unfold thetaACoefficient
  push_cast
  ring

def evalThetaAWithCoefficient (cfg : BallConfig) (N : ℕ)
    (bt ba bc bz : ComplexBall) : Option ComplexBall := do
  let bv := complexArgumentBall cfg bz
  let bm := roundedAdd cfg.prec bv (neg (verticalArgumentBall cfg ba))
  let sm ← evalThetaFast cfg 0 N bt bm
  let sz ← evalThetaFast cfg 0 N bt bv
  let sz1 ← evalThetaFast cfg 1 N bt bv
  let iz ← checkedInv cfg.prec sz
  let r := roundedMul cfg.prec sm iz
  let rz := roundedMul cfg.prec sz1 iz
  let e ← checkedExp cfg.prec cfg.terms cfg.squarings
    (roundedMul cfg.prec (roundedMul cfg.prec
      (roundedAdd cfg.prec ba (rational (-1))) piBall) rz)
  pure (roundedMul cfg.prec (roundedMul cfg.prec bc (roundedMul cfg.prec r r)) e)

theorem evalThetaAWithCoefficient_sound {bt ba bc bz : ComplexBall} {t a : ℝ} {z : ℂ}
    (ht : bt.Contains (t : ℂ)) (ha : ba.Contains (a : ℂ))
    (hc : bc.Contains (thetaACoefficient t a)) (hz : bz.Contains z)
    (cfg : BallConfig) (N : ℕ) :
    Sound (evalThetaAWithCoefficient cfg N bt ba bc bz) (thetaA t a z) := by
  have hv := complexArgumentBall_contains hz cfg
  have hm : (roundedAdd cfg.prec (complexArgumentBall cfg bz)
      (neg (verticalArgumentBall cfg ba))).Contains (Real.pi*(z-a)/2) := by
    convert roundedAdd_contains hv (neg_contains (verticalArgumentBall_contains ha cfg)) cfg.prec using 1
    ring
  unfold evalThetaAWithCoefficient
  apply bind_sound (evalThetaFast_sound ht hm cfg 0 N)
  intro sm hsm
  apply bind_sound (evalThetaFast_sound ht hv cfg 0 N)
  intro sz hsz
  apply bind_sound (evalThetaFast_sound ht hv cfg 1 N)
  intro sz1 hsz1
  apply bind_sound (checkedInv_sound hsz cfg.prec)
  intro iz hiz
  have hr := roundedMul_contains hsm hiz cfg.prec
  have hrz := roundedMul_contains hsz1 hiz cfg.prec
  have hexp := roundedMul_contains (roundedMul_contains
    (roundedAdd_contains ha (rational_contains (-1)) cfg.prec) piBall_contains cfg.prec) hrz cfg.prec
  apply bind_sound (checkedExp_sound hexp cfg.prec cfg.terms cfg.squarings)
  intro e he
  apply sound_some
  convert roundedMul_contains (roundedMul_contains hc (roundedMul_contains hr hr cfg.prec) cfg.prec)
    he cfg.prec using 1
  unfold thetaA thetaQuotient thetaACoefficient
  push_cast
  simp only [div_eq_mul_inv, sub_eq_add_neg, pow_two]

def evalThetaA (cfg : BallConfig) (N : ℕ) (bt ba bz : ComplexBall) : Option ComplexBall :=
  (evalThetaACoefficient cfg N bt ba).bind (fun bc => evalThetaAWithCoefficient cfg N bt ba bc bz)

theorem evalThetaA_sound {bt ba bz : ComplexBall} {t a : ℝ} {z : ℂ}
    (ht : bt.Contains (t : ℂ)) (ha : ba.Contains (a : ℂ)) (hz : bz.Contains z)
    (cfg : BallConfig) (N : ℕ) : Sound (evalThetaA cfg N bt ba bz) (thetaA t a z) :=
  bind_sound (evalThetaACoefficient_sound ht ha cfg N) _
    (fun _ hc => evalThetaAWithCoefficient_sound ht ha hc hz cfg N)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.evalThetaA_sound
