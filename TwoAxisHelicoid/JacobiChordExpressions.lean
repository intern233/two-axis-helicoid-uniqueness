import TwoAxisHelicoid.JacobiChordKernel
import TwoAxisHelicoid.JacobiExpressionValues

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 1000000
attribute [local irreducible] jacobiPairProduct jacobiFactorProduct jacobiNormalization
attribute [local simp] neg_div

@[local simp] private theorem chord_const_i : (⟨(0 : ℝ),1⟩ : ℂ) = I := rfl

def jacobiChordNomeExpression : BallExpression :=
  .exp (.neg (.div .pi (.mul (.rational 2) (.input 0))))
def jacobiChordHExpression : BallExpression :=
  .div (.mul (.rational 2) (.input 0)) (.add (.rational 1) (.pow (.input 0) 2))
def jacobiChordKExpression : BallExpression :=
  .div (.sub (.rational 1) (.pow (.input 0) 2)) (.add (.rational 1) (.pow (.input 0) 2))
def jacobiChordUExpression : BallExpression :=
  .add (.input 0) (.mul (.mul (.const ⟨0,1⟩) (.input 1)) (.input 2))
def jacobiChordXExpression : BallExpression :=
  .div (.add (.input 0) (.const ⟨0,1⟩)) (.sub (.input 0) (.const ⟨0,1⟩))
def jacobiChordInvXExpression : BallExpression :=
  .div (.sub (.input 0) (.const ⟨0,1⟩)) (.add (.input 0) (.const ⟨0,1⟩))
def jacobiChordQXExpression : BallExpression := .mul (.input 0) (.input 3)
def jacobiChordQInvXExpression : BallExpression := .mul (.input 0) (.input 4)
def jacobiChordQRXExpression : BallExpression := .mul (.mul (.input 0) (.input 1)) (.input 3)
def jacobiChordQInvRXExpression : BallExpression := .mul (.neg (.input 2)) (.input 4)
def jacobiChordRXExpression : BallExpression := .mul (.input 1) (.input 3)

/-- Inputs: t, kappa, normalization, u, x, rx, four products, two Euler sums, chord k. -/
def jacobiChordResultExpression : BallExpression :=
  let d := BallExpression.mul (.input 6) (.input 7)
  let ds := BallExpression.mul (.input 8) (.input 9)
  let j := BallExpression.sub (.input 10) (.input 11)
  .mul (.mul (.mul (.mul (.div (.neg .pi) (.mul (.rational 2) (.input 0))) (.input 2)) (.input 4))
    (.pow (.div (.mul (.sub (.rational 1) (.input 5)) ds) d) 2))
    (.mul (.exp (.mul (.input 1) (.sub (.mul (.const ⟨0,1⟩) (.input 3)) (.mul (.rational 2) j))))
      (.input 12))

noncomputable def jacobiChordResult (t k c u x rx pA pB pC pD eA eB kc : ℂ) : ℂ :=
  (-(Real.pi : ℂ)/(2*t))*c*x*(((1-rx)*(pC*pD))/(pA*pB))^2*
    Complex.exp (k*(I*u-2*(eA-eB)))*kc

theorem value_jacobiChordNomeExpression (t : ℝ) :
    jacobiChordNomeExpression.value (complexInputList [(t : ℂ)]) = (leftNome t : ℂ) := by
  simp [jacobiChordNomeExpression, BallExpression.value, complexInputList, leftNome]


theorem value_jacobiChordHExpression (q : ℝ) :
    jacobiChordHExpression.value (complexInputList [(q : ℂ)]) = (leftChordH q : ℂ) := by
  simp [jacobiChordHExpression, BallExpression.value, complexInputList, leftChordH]

theorem value_jacobiChordKExpression (q : ℝ) :
    jacobiChordKExpression.value (complexInputList [(q : ℂ)]) = (leftChordK q : ℂ) := by
  simp [jacobiChordKExpression, BallExpression.value, complexInputList, leftChordK]

theorem value_jacobiChordUExpression (t : ℝ) (z : ℂ) :
    jacobiChordUExpression.value (complexInputList
      [(leftChordH (leftNome t) : ℂ),(leftChordK (leftNome t) : ℂ),z]) = jacobiChordPoint t z := by
  simp [jacobiChordUExpression, BallExpression.value, complexInputList, jacobiChordPoint, QComplex.val]

theorem value_jacobiChordXExpression (u : ℂ) :
    jacobiChordXExpression.value (complexInputList [u]) = jacobiChordX u := by
  simp [jacobiChordXExpression, BallExpression.value, complexInputList, jacobiChordX, QComplex.val]

theorem value_jacobiChordInvXExpression (u : ℂ) :
    jacobiChordInvXExpression.value (complexInputList [u]) = (jacobiChordX u)⁻¹ := by
  simp [jacobiChordInvXExpression, BallExpression.value, complexInputList, jacobiChordX, QComplex.val, inv_div]

theorem value_jacobiChordSeeds (t a : ℝ) (x : ℂ) :
    let env := complexInputList [jacobiNome (1/t),(dualProductR t a : ℂ),
      Complex.exp (-(dualProductKappa t a : ℂ)),x,x⁻¹]
    jacobiChordQXExpression.value env = jacobiNome (1/t)*x ∧
    jacobiChordQInvXExpression.value env = jacobiNome (1/t)*x⁻¹ ∧
    jacobiChordQRXExpression.value env = jacobiNome (1/t)*((dualProductR t a : ℂ)*x) ∧
    jacobiChordQInvRXExpression.value env = jacobiNome (1/t)*((dualProductR t a : ℂ)*x)⁻¹ ∧
    jacobiChordRXExpression.value env = (dualProductR t a : ℂ)*x := by
  simp [jacobiChordQXExpression, jacobiChordQInvXExpression, jacobiChordQRXExpression,
    jacobiChordQInvRXExpression, jacobiChordRXExpression, BallExpression.value,
    complexInputList, ← dual_q_div_r, div_eq_mul_inv, mul_assoc, mul_inv_rev,
    mul_comm]

theorem value_jacobiChordResultExpression (t k c u x rx pA pB pC pD eA eB kc : ℂ) :
    jacobiChordResultExpression.value (complexInputList [t,k,c,u,x,rx,pA,pB,pC,pD,eA,eB,kc]) =
      jacobiChordResult t k c u x rx pA pB pC pD eA eB kc := by
  simp [jacobiChordResultExpression, jacobiChordResult, BallExpression.value, complexInputList,
    QComplex.val, mul_assoc]

private theorem chord_scale_algebra (t k c x y A B : ℂ) :
    (I*k)*(((I*(Real.pi : ℂ)/(2*t))*x*A)*(c*y^2*B)) =
      (-(Real.pi : ℂ)/(2*t))*c*x*y^2*(A*B)*k := by
  calc
    _ = (I*I)*((Real.pi : ℂ)/(2*t)*c*x*y^2*(A*B)*k) := by ring
    _ = _ := by rw [I_mul_I]; ring

theorem jacobiChordKernel_eq_result {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (hx0 : jacobiChordX (jacobiChordPoint t z) ≠ 0)
    (hp : ‖jacobiNome (1/t)‖*‖jacobiChordX (jacobiChordPoint t z)‖ < 1)
    (hm : ‖jacobiNome (1/t)‖*‖(jacobiChordX (jacobiChordPoint t z))⁻¹‖ < 1) :
    let Q := jacobiNome (1/t)
    let r := (dualProductR t a : ℂ)
    let u := jacobiChordPoint t z
    let x := jacobiChordX u
    jacobiChordKernel t a z = jacobiChordResult t (dualProductKappa t a)
      (jacobiNormalization Q r) u x (r*x)
      (jacobiFactorProduct Q x) (jacobiFactorProduct Q x⁻¹)
      (jacobiFactorProduct Q (r*x)) (jacobiFactorProduct Q (r*x)⁻¹)
      (x*logDeriv (jacobiFactorProduct Q) x)
      (x⁻¹*logDeriv (jacobiFactorProduct Q) x⁻¹) (leftChordK (leftNome t)) := by
  dsimp only
  have hlog := jacobiPairProduct_euler_logDeriv
    (jacobiNome_norm_lt_one (one_div_pos.mpr ht)) hx0 hp hm
  let u := jacobiChordPoint t z
  let x := jacobiChordX u
  let κ := (dualProductKappa t a : ℂ)
  let Q := jacobiNome (1/t)
  have he : I*κ*u+(-2*κ*x*logDeriv (jacobiPairProduct Q) x) =
      κ*(I*u-2*(x*logDeriv (jacobiFactorProduct Q) x-
        x⁻¹*logDeriv (jacobiFactorProduct Q) x⁻¹)) := by
    calc
      _ = κ*(I*u-2*(x*logDeriv (jacobiPairProduct Q) x)) := by ring
      _ = _ := by rw [hlog]
  have he' := congrArg Complex.exp he
  rw [Complex.exp_add] at he'
  unfold jacobiChordKernel jacobiChordDifferential leftChordDifferential jacobiProductError
    jacobiChordResult
  change (I*(leftChordK (leftNome t) : ℂ))*
    (((I*(Real.pi : ℂ)/(2*(t : ℂ)))*x*Complex.exp (I*κ*u))*
      (jacobiNormalization Q (dualProductR t a)*
        (((1-(dualProductR t a : ℂ)*x)*jacobiPairProduct Q ((dualProductR t a : ℂ)*x))/
          jacobiPairProduct Q x)^2*
        Complex.exp (-2*κ*x*logDeriv (jacobiPairProduct Q) x))) = _
  rw [chord_scale_algebra, he']
  unfold jacobiPairProduct
  rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiChordKernel_eq_result
