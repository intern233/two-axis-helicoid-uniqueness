import TwoAxisHelicoid.SpinorNormalization
import TwoAxisHelicoid.QuaternionFrameCover
import TwoAxisHelicoid.HolomorphicNullImmersion

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 1000000

noncomputable def normalizedSpinorFrame (s : NonzeroSpinor) : OrthonormalTangentPair :=
  unitSpinorTangentFrame (normalizeSpinor s)

theorem normalizedSpinorFrame_continuous : Continuous normalizedSpinorFrame :=
  (unitNullTangentPairHomeomorph.continuous.comp unitSpinorQuadratic_continuous).comp
    normalizeSpinor_continuous

theorem normalizedSpinorFrame_vectors (s : NonzeroSpinor) :
    (normalizedSpinorFrame s).1 =
      ((spinorWeight s.1)⁻¹ • nullRealDerivative (spinorQuadratic s.1) 1,
       (spinorWeight s.1)⁻¹ • nullRealDerivative (spinorQuadratic s.1) I) := by
  change ((fun j => (spinorQuadratic (normalizeSpinor s).1 j).re),
    (fun j => -(spinorQuadratic (normalizeSpinor s).1 j).im)) = _
  rw [normalizeSpinor_quadratic]
  apply Prod.ext <;> funext j <;> simp [Complex.mul_re,Complex.mul_im]

/-- The lift covers the normalized derivative frame of the actual map,
with the orientation determined by the complex coordinate. -/
theorem normalizedSpinorFrame_actual_derivative {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (s : NonzeroSpinor) (hX : HasFDerivAt X (nullRealDerivative (spinorQuadratic s.1)) z) :
    (normalizedSpinorFrame s).1 =
      ((spinorWeight s.1)⁻¹ • fderiv ℝ X z 1,
       (spinorWeight s.1)⁻¹ • fderiv ℝ X z I) := by
  rw [hX.fderiv]
  exact normalizedSpinorFrame_vectors s

noncomputable def normalizedQuaternionLift (s : NonzeroSpinor) : UnitQuaternion :=
  unitSpinorQuaternionHomeomorph (normalizeSpinor s)

theorem normalizedQuaternionLift_continuous : Continuous normalizedQuaternionLift :=
  unitSpinorQuaternionHomeomorph.continuous.comp normalizeSpinor_continuous

theorem normalizedQuaternionLift_covers (s : NonzeroSpinor) :
    unitQuaternionFrame (normalizedQuaternionLift s) = normalizedSpinorFrame s :=
  unitQuaternionFrame_spinor (normalizeSpinor s)

theorem normalizedSpinorFrame_neg (s : NonzeroSpinor) :
    normalizedSpinorFrame ⟨-s.1,neg_ne_zero.mpr s.2⟩ = normalizedSpinorFrame s := by
  unfold normalizedSpinorFrame
  rw [normalizeSpinor_neg]
  exact unitSpinorTangentFrame_fibers.mpr (Or.inr rfl)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.normalizedSpinorFrame_actual_derivative
#print axioms TwoAxisHelicoid.normalizedQuaternionLift_covers
