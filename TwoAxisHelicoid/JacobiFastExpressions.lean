import TwoAxisHelicoid.JacobiExpressionValues

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000

def jacobiFastX (right : Bool) : BallExpression :=
  if right then .inv (.input 3) else .input 3

def jacobiFastInvX (right : Bool) : BallExpression :=
  if right then .input 3 else .inv (.input 3)

def jacobiFastQXExpression (right : Bool) : BallExpression :=
  .mul (.input 0) (jacobiFastX right)

def jacobiFastQInvXExpression (right : Bool) : BallExpression :=
  .mul (.input 0) (jacobiFastInvX right)

def jacobiFastQRXExpression (right : Bool) : BallExpression :=
  .mul (.mul (.input 0) (.input 1)) (jacobiFastX right)

def jacobiFastQInvRXExpression (right : Bool) : BallExpression :=
  .mul (.neg (.input 2)) (jacobiFastInvX right)

def jacobiFastRXExpression (right : Bool) : BallExpression :=
  .mul (.input 1) (jacobiFastX right)

theorem value_jacobiFastSeeds (right : Bool) (t a : ℝ) (z : ℂ) :
    let q := jacobiNome (1/t)
    let r := (dualProductR t a : ℂ)
    let x := physicalJacobiX t z
    let env := complexInputList [q,r,Complex.exp (-(dualProductKappa t a : ℂ)),
      if right then x⁻¹ else x]
    (jacobiFastQXExpression right).value env = q*x ∧
    (jacobiFastQInvXExpression right).value env = q*x⁻¹ ∧
    (jacobiFastQRXExpression right).value env = q*(r*x) ∧
    (jacobiFastQInvRXExpression right).value env = q*(r*x)⁻¹ ∧
    (jacobiFastRXExpression right).value env = r*x := by
  cases right <;>
    simp [jacobiFastQXExpression, jacobiFastQInvXExpression, jacobiFastQRXExpression,
      jacobiFastQInvRXExpression, jacobiFastRXExpression, jacobiFastX, jacobiFastInvX,
      complexInputList, BallExpression.value, ← dual_q_div_r, div_eq_mul_inv,
      mul_assoc, mul_inv_rev, mul_comm, mul_left_comm]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.value_jacobiFastSeeds
