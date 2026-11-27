import TwoAxisHelicoid.SpinorQuadraticMap
import Mathlib.Analysis.Quaternion
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace TwoAxisHelicoid
open Complex
open scoped Quaternion
set_option maxHeartbeats 1000000

/-- A fixed real linear change of the four spinor coordinates. With this
convention quaternion conjugation produces the actual oriented tangent
vectors `Re Φ` and `-Im Φ` of the Weierstrass immersion. -/
def spinorQuaternion (s : ℂ × ℂ) : ℍ := ⟨-s.1.im,s.2.re,-s.2.im,s.1.re⟩

noncomputable def spinorQuaternionLinearEquiv : (ℂ × ℂ) ≃ₗ[ℝ] ℍ where
  toFun := spinorQuaternion
  invFun q := (⟨q.imK,-q.re⟩,⟨q.imI,-q.imJ⟩)
  left_inv s := by
    apply Prod.ext <;> apply Complex.ext <;> simp [spinorQuaternion]
  right_inv q := by
    ext <;> simp [spinorQuaternion]
  map_add' s t := by
    ext <;> simp [spinorQuaternion,add_comm]
  map_smul' r s := by
    ext <;> simp [spinorQuaternion]

noncomputable def spinorQuaternionHomeomorph : (ℂ × ℂ) ≃ₜ ℍ :=
  spinorQuaternionLinearEquiv.toContinuousLinearEquiv.toHomeomorph

theorem spinorQuaternion_normSq (s : ℂ × ℂ) : Quaternion.normSq (spinorQuaternion s) = spinorWeight s := by
  simp [Quaternion.normSq_def',spinorQuaternion,spinorWeight,Complex.normSq_apply]
  ring

def quaternionImaginaryVector (q : ℍ) : Fin 3 → ℝ := ![q.imI,q.imJ,q.imK]
def quaternionAxisI : ℍ := ⟨0,1,0,0⟩
def quaternionAxisJ : ℍ := ⟨0,0,1,0⟩

theorem spinorQuaternion_axisI (s : ℂ × ℂ) :
    quaternionImaginaryVector (spinorQuaternion s*quaternionAxisI*star (spinorQuaternion s)) =
      fun j => (spinorQuadratic s j).re := by
  ext j
  fin_cases j <;>
    simp [quaternionImaginaryVector,spinorQuaternion,quaternionAxisI,spinorQuadratic,
      pow_two,Complex.mul_re,Complex.mul_im] <;> ring

theorem spinorQuaternion_axisJ (s : ℂ × ℂ) :
    quaternionImaginaryVector (spinorQuaternion s*quaternionAxisJ*star (spinorQuaternion s)) =
      fun j => -(spinorQuadratic s j).im := by
  ext j
  fin_cases j <;>
    simp [quaternionImaginaryVector,spinorQuaternion,quaternionAxisJ,spinorQuadratic,
      pow_two,Complex.mul_re,Complex.mul_im] <;> ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.spinorQuaternion_axisI
#print axioms TwoAxisHelicoid.spinorQuaternion_axisJ
