import TwoAxisHelicoid.JacobiKernelExpressions

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct jacobiPairProduct jacobiNormalization
attribute [local simp] neg_div

@[local simp] private theorem const_i : (⟨(0 : ℝ),1⟩ : ℂ) = I := rfl
@[local simp] private theorem const_neg_i : (⟨(0 : ℝ),-1⟩ : ℂ) = -I := by
  apply Complex.ext <;> norm_num

theorem value_jacobiDualNomeExpression (t a : ℝ) (z : ℂ) :
    jacobiDualNomeExpression.value (complexInputList [t,a,z]) = jacobiNome (1/t) := by
  rw [dual_nome_complex]
  simp [jacobiDualNomeExpression, BallExpression.value, complexInputList]

theorem value_jacobiDualRExpression (t a : ℝ) (z : ℂ) :
    jacobiDualRExpression.value (complexInputList [t,a,z]) = (dualProductR t a : ℂ) := by
  rw [dual_r_complex]
  simp [jacobiDualRExpression, BallExpression.value, complexInputList]

theorem value_jacobiDualKappaExpression (t a : ℝ) (z : ℂ) :
    jacobiDualKappaExpression.value (complexInputList [t,a,z]) = (dualProductKappa t a : ℂ) := by
  simp [jacobiDualKappaExpression, BallExpression.value, complexInputList, dualProductKappa]

theorem value_jacobiDualBetaExpression (t a : ℝ) (z : ℂ) :
    jacobiDualBetaExpression.value (complexInputList [t,a,z]) =
      Complex.exp (-(dualProductKappa t a : ℂ)) := by
  change Complex.exp (-jacobiDualKappaExpression.value _) = _
  rw [value_jacobiDualKappaExpression]

theorem value_jacobiQXExpression (t a : ℝ) (z : ℂ) :
    jacobiQXExpression.value (complexInputList [t,a,z]) = jacobiNome (1/t)*physicalJacobiX t z := by
  rw [physical_qx t z]
  simp [jacobiQXExpression, BallExpression.value, complexInputList, QComplex.val]

theorem value_jacobiQInvXExpression (t a : ℝ) (z : ℂ) :
    jacobiQInvXExpression.value (complexInputList [t,a,z]) = jacobiNome (1/t)*(physicalJacobiX t z)⁻¹ := by
  rw [physical_qx_inv t z]
  simp [jacobiQInvXExpression, BallExpression.value, complexInputList, QComplex.val]

theorem value_jacobiQRXExpression (t a : ℝ) (z : ℂ) :
    jacobiQRXExpression.value (complexInputList [t,a,z]) = jacobiNome (1/t)*((dualProductR t a : ℂ)*physicalJacobiX t z) := by
  rw [physical_qrx t a z]
  simp [jacobiQRXExpression, BallExpression.value, complexInputList, QComplex.val]

theorem value_jacobiQInvRXExpression (t a : ℝ) (z : ℂ) :
    jacobiQInvRXExpression.value (complexInputList [t,a,z]) = jacobiNome (1/t)*((dualProductR t a : ℂ)*physicalJacobiX t z)⁻¹ := by
  rw [physical_qrx_inv t a z]
  simp [jacobiQInvRXExpression, BallExpression.value, complexInputList, QComplex.val]

theorem value_jacobiPhysicalRXExpression (t a : ℝ) (z : ℂ) :
    jacobiPhysicalRXExpression.value (complexInputList [t,a,z]) = (dualProductR t a : ℂ)*physicalJacobiX t z := by
  rw [physical_rx t a z]
  simp [jacobiPhysicalRXExpression, BallExpression.value, complexInputList, QComplex.val]

theorem value_jacobiPhysicalXExpression (right : Bool) (t a : ℝ) (z : ℂ) :
    (jacobiPhysicalXExpression right).value (complexInputList [t,a,z]) =
      if right then (physicalJacobiX t z)⁻¹ else physicalJacobiX t z := by
  cases right
  · simp [jacobiPhysicalXExpression, BallExpression.value, complexInputList, QComplex.val,
      physicalJacobiX]
  · simp [jacobiPhysicalXExpression, BallExpression.value, complexInputList, QComplex.val,
      physicalJacobiX_inv]

theorem value_jacobiNormalizationExpression (q r : ℂ) :
    jacobiNormalizationExpression.value (complexInputList [r,
      jacobiFactorProduct q 1, jacobiFactorProduct q r, jacobiFactorProduct q r⁻¹]) =
      jacobiNormalization q r := by
  unfold jacobiNormalization jacobiPairProduct
  simp [jacobiNormalizationExpression, BallExpression.value, complexInputList]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.value_jacobiNormalizationExpression

