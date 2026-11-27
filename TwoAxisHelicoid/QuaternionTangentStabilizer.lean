import TwoAxisHelicoid.TangentPairNormalRotation

namespace TwoAxisHelicoid
open Complex Matrix
open scoped Quaternion Matrix

def quaternionAxisK : ℍ := ⟨0,0,0,1⟩

/-- The subgroup of ambient unit quaternions fixing the third reference
axis under conjugation is the standard circle in the real–K plane. -/
noncomputable def tangentSpinQuaternion (u : Circle) : UnitQuaternion :=
  ⟨⟨(u : ℂ).re,0,0,(u : ℂ).im⟩,by
    simpa [Quaternion.normSq_def',Complex.normSq_apply,pow_two] using u.normSq_coe⟩

theorem tangentSpinQuaternion_mul (u v : Circle) :
    (tangentSpinQuaternion (u*v)).1 =
      (tangentSpinQuaternion u).1*(tangentSpinQuaternion v).1 := by
  ext <;> simp [tangentSpinQuaternion,Complex.mul_re,Complex.mul_im]

/-- The phase action is concretely right multiplication by the standard
Spin(2) subgroup inside Spin(3). -/
theorem spinCircleAction_quaternion (u : Circle) (q : UnitQuaternion) :
    (spinCircleAction u q).1 = q.1*(tangentSpinQuaternion u).1 := by
  obtain ⟨s,rfl⟩ := unitSpinorQuaternionHomeomorph.surjective q
  rw [spinCircleAction,unitQuaternionPhase_spinor]
  change spinorQuaternion ((u : ℂ) • s.1) = spinorQuaternion s.1*(tangentSpinQuaternion u).1
  ext <;> simp [tangentSpinQuaternion,spinorQuaternion,Complex.mul_re,Complex.mul_im] <;> ring

theorem tangentSpinQuaternion_commutes_axisK (u : Circle) :
    (tangentSpinQuaternion u).1*quaternionAxisK = quaternionAxisK*(tangentSpinQuaternion u).1 := by
  ext <;> simp [tangentSpinQuaternion,quaternionAxisK]

theorem unitQuaternion_commutes_axisK_iff (q : UnitQuaternion) :
    q.1*quaternionAxisK = quaternionAxisK*q.1 ↔ ∃ u : Circle, tangentSpinQuaternion u = q := by
  constructor
  · intro h
    have hi := congrArg (fun q : ℍ => q.imI) h
    have hj := congrArg (fun q : ℍ => q.imJ) h
    simp [quaternionAxisK] at hi hj
    have hx : q.1.imI = 0 := by linarith
    have hy : q.1.imJ = 0 := by linarith
    let z : ℂ := ⟨q.1.re,q.1.imK⟩
    have hz : Complex.normSq z = 1 := by
      simpa [z,Quaternion.normSq_def',Complex.normSq_apply,hx,hy,pow_two] using q.2
    let u : Circle := ⟨z,mem_sphere_zero_iff_norm.mpr (by rw [Complex.norm_def,hz,Real.sqrt_one])⟩
    refine ⟨u,Subtype.ext ?_⟩
    ext <;> simp [tangentSpinQuaternion,u,z,hx,hy]
  · rintro ⟨u,rfl⟩
    exact tangentSpinQuaternion_commutes_axisK u

theorem conjugated_axes_cross (q : ℍ) :
    quaternionImaginaryVector (q*quaternionAxisI*star q) ⨯₃
      quaternionImaginaryVector (q*quaternionAxisJ*star q) =
      Quaternion.normSq q • quaternionImaginaryVector (q*quaternionAxisK*star q) := by
  rw [cross_apply]
  funext j
  fin_cases j <;> simp [quaternionImaginaryVector,quaternionAxisI,quaternionAxisJ,quaternionAxisK,
    Quaternion.normSq_def'] <;> ring

/-- The oriented derivative normal is exactly the third column of the
ambient quaternion rotation. -/
theorem unitQuaternionFrame_normal_axisK (q : UnitQuaternion) :
    tangentPairNormal (unitQuaternionFrame q) = quaternionImaginaryVector (q.1*quaternionAxisK*star q.1) := by
  rw [tangentPairNormal,unitQuaternionFrame_axisI,unitQuaternionFrame_axisJ,
    conjugated_axes_cross,q.2,one_smul]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spinCircleAction_quaternion
#print axioms TwoAxisHelicoid.unitQuaternion_commutes_axisK_iff
#print axioms TwoAxisHelicoid.unitQuaternionFrame_normal_axisK
