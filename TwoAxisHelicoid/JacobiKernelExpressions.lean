import TwoAxisHelicoid.JacobiPhysicalCoordinates
import TwoAxisHelicoid.DyadicInputList

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct jacobiNormalization

def jacobiDualNomeExpression : BallExpression := .neg (.exp (.neg (.div .pi (.input 0))))
def jacobiDualRExpression : BallExpression := .exp (.neg (.div (.mul .pi (.input 1)) (.input 0)))
def jacobiDualKappaExpression : BallExpression :=
  .div (.mul .pi (.sub (.rational 1) (.input 1))) (.input 0)
def jacobiDualBetaExpression : BallExpression := .exp (.neg jacobiDualKappaExpression)
def jacobiQXExpression : BallExpression :=
  .mul (.const ⟨0,-1⟩) (.exp (.div (.mul .pi (.sub (.input 2) (.rational 1))) (.input 0)))
def jacobiQInvXExpression : BallExpression :=
  .mul (.const ⟨0,1⟩) (.exp (.neg (.div (.mul .pi (.add (.input 2) (.rational 1))) (.input 0))))
def jacobiQRXExpression : BallExpression :=
  .mul (.const ⟨0,-1⟩) (.exp (.div (.mul .pi (.sub (.sub (.input 2) (.input 1)) (.rational 1))) (.input 0)))
def jacobiQInvRXExpression : BallExpression :=
  .mul (.const ⟨0,1⟩) (.exp (.div (.mul .pi (.sub (.sub (.input 1) (.input 2)) (.rational 1))) (.input 0)))
def jacobiPhysicalXExpression (right : Bool) : BallExpression :=
  if right then .mul (.const ⟨0,-1⟩) (.exp (.neg (.div (.mul .pi (.input 2)) (.input 0))))
  else .mul (.const ⟨0,1⟩) (.exp (.div (.mul .pi (.input 2)) (.input 0)))
def jacobiPhysicalRXExpression : BallExpression :=
  .mul (.const ⟨0,1⟩) (.exp (.div (.mul .pi (.sub (.input 2) (.input 1))) (.input 0)))

def jacobiNormalizationExpression : BallExpression :=
  .div (.pow (.input 1) 4)
    (.mul (.pow (.sub (.rational 1) (.input 0)) 2) (.pow (.mul (.input 2) (.input 3)) 2))

/-- Inputs: t, kappa, normalization, x (or 1/x), rx, four products, two Euler sums. -/
def jacobiKernelResultExpression (right : Bool) : BallExpression :=
  let u := BallExpression.inv (.sub (.rational 1) (.input 3))
  let v := if right then BallExpression.neg u else .mul (.input 3) u
  let b := if right then BallExpression.sub (.rational 1) (.mul (.rational 2) u)
    else .add (.rational (-1)) (.mul (.rational 2) u)
  let d := BallExpression.mul (.input 5) (.input 6)
  let ds := BallExpression.mul (.input 7) (.input 8)
  let j := BallExpression.sub (.input 9) (.input 10)
  .mul (.mul (.mul (.div (.pow .pi 2) (.pow (.input 0) 2)) (.input 2)) (.pow v 2))
    (.mul (.pow (.div (.mul (.sub (.rational 1) (.input 4)) ds) d) 2)
      (.exp (.mul (.input 1) (.sub b (.mul (.rational 2) j)))))

noncomputable def jacobiKernelResult (right : Bool)
    (t k c x rx pA pB pC pD eA eB : ℂ) : ℂ :=
  let u := (1-x)⁻¹
  let v := if right then -u else x*u
  let b := if right then 1-2*u else -1+2*u
  ((Real.pi : ℂ)^2/t^2)*c*v^2*
    (((1-rx)*(pC*pD))/(pA*pB))^2*Complex.exp (k*(b-2*(eA-eB)))

theorem value_jacobiKernelResultExpression (right : Bool)
    (t k c x rx pA pB pC pD eA eB : ℂ) :
    (jacobiKernelResultExpression right).value
      (complexInputList [t,k,c,x,rx,pA,pB,pC,pD,eA,eB]) =
      jacobiKernelResult right t k c x rx pA pB pC pD eA eB := by
  cases right <;>
    simp [jacobiKernelResultExpression, jacobiKernelResult, BallExpression.value, complexInputList,
      mul_assoc]

theorem jacobiKernelResult_inverse {x : ℂ} (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (t k c rx pA pB pC pD eA eB : ℂ) :
    jacobiKernelResult true t k c x⁻¹ rx pA pB pC pD eA eB =
      jacobiKernelResult false t k c x rx pA pB pC pD eA eB := by
  have h1 : 1-x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hi : 1-x⁻¹ ≠ 0 := by
    intro h
    exact hx1 (inv_eq_one.mp (sub_eq_zero.mp h).symm)
  have hv : -(1-x⁻¹)⁻¹ = x*(1-x)⁻¹ := by field_simp; ring
  have hb : 1-2*(1-x⁻¹)⁻¹ = -1+2*(1-x)⁻¹ := by field_simp; ring
  simp only [jacobiKernelResult, ite_true, Bool.false_eq_true, ite_false, hv, hb]

theorem dualProductIntegrand_eq_kernelResult {t a : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z+I*((t/2 : ℝ) : ℂ) ∉ (rhombicPeriodPair t ht).lattice)
    (hp : ‖jacobiNome (1/t)‖*‖physicalJacobiX t z‖ < 1)
    (hm : ‖jacobiNome (1/t)‖*‖(physicalJacobiX t z)⁻¹‖ < 1) (right : Bool) :
    dualProductIntegrand t a (physicalDualCoordinate t z) =
      jacobiKernelResult right t (dualProductKappa t a)
        (jacobiNormalization (jacobiNome (1/t)) (dualProductR t a))
        (if right then (physicalJacobiX t z)⁻¹ else physicalJacobiX t z)
        ((dualProductR t a : ℂ)*physicalJacobiX t z)
        (jacobiFactorProduct (jacobiNome (1/t)) (physicalJacobiX t z))
        (jacobiFactorProduct (jacobiNome (1/t)) (physicalJacobiX t z)⁻¹)
        (jacobiFactorProduct (jacobiNome (1/t)) ((dualProductR t a : ℂ)*physicalJacobiX t z))
        (jacobiFactorProduct (jacobiNome (1/t)) ((dualProductR t a : ℂ)*physicalJacobiX t z)⁻¹)
        (physicalJacobiX t z*logDeriv (jacobiFactorProduct (jacobiNome (1/t))) (physicalJacobiX t z))
        ((physicalJacobiX t z)⁻¹*logDeriv (jacobiFactorProduct (jacobiNome (1/t))) (physicalJacobiX t z)⁻¹) := by
  have hx0 := physicalJacobiX_ne_zero t z
  have hx1 := physicalJacobiX_ne_one ht hz
  have hlog := jacobiPairProduct_euler_logDeriv (jacobiNome_norm_lt_one (one_div_pos.mpr ht)) hx0 hp hm
  cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals try rw [jacobiKernelResult_inverse hx0 hx1]
  all_goals
    simp only [jacobiKernelResult, Bool.false_eq_true, ite_false]
    unfold dualProductIntegrand
    rw [physicalJacobiX_eq]
    have he : -1+2/(1-physicalJacobiX t z)-2*physicalJacobiX t z*
        logDeriv (jacobiPairProduct (jacobiNome (1/t))) (physicalJacobiX t z) =
        -1+2*(1-physicalJacobiX t z)⁻¹-2*(physicalJacobiX t z*
          logDeriv (jacobiFactorProduct (jacobiNome (1/t))) (physicalJacobiX t z)-
          (physicalJacobiX t z)⁻¹*logDeriv (jacobiFactorProduct (jacobiNome (1/t))) (physicalJacobiX t z)⁻¹) := by
      rw [mul_assoc (2 : ℂ), hlog]
      rfl
    rw [he]
    unfold jacobiPairProduct
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.dualProductIntegrand_eq_kernelResult
