import TwoAxisHelicoid.SpinorQuaternion
import TwoAxisHelicoid.OrthonormalFrameCover

namespace TwoAxisHelicoid
open scoped Quaternion
set_option maxHeartbeats 1000000

abbrev UnitQuaternion := {q : ℍ // Quaternion.normSq q = 1}

noncomputable def unitSpinorQuaternionHomeomorph : UnitSpinor ≃ₜ UnitQuaternion :=
  spinorQuaternionHomeomorph.subtype (fun s => by
    change spinorWeight s = 1 ↔ Quaternion.normSq (spinorQuaternion s) = 1
    rw [spinorQuaternion_normSq])

/-- Quaternion conjugation acting on the first two coordinate axes.
The following two identities identify this transported definition with
the explicit standard quaternion action. -/
noncomputable def unitQuaternionFrame : UnitQuaternion → OrthonormalTangentPair :=
  unitSpinorTangentFrame ∘ unitSpinorQuaternionHomeomorph.symm

theorem unitQuaternionFrame_axisI (q : UnitQuaternion) :
    (unitQuaternionFrame q).1.1 =
      quaternionImaginaryVector (q.1*quaternionAxisI*star q.1) := by
  have he := congrArg Subtype.val (unitSpinorQuaternionHomeomorph.apply_symm_apply q)
  change spinorQuaternion (unitSpinorQuaternionHomeomorph.symm q).1 = q.1 at he
  change (fun j => (spinorQuadratic (unitSpinorQuaternionHomeomorph.symm q).1 j).re) = _
  rw [← spinorQuaternion_axisI,he]

theorem unitQuaternionFrame_axisJ (q : UnitQuaternion) :
    (unitQuaternionFrame q).1.2 =
      quaternionImaginaryVector (q.1*quaternionAxisJ*star q.1) := by
  have he := congrArg Subtype.val (unitSpinorQuaternionHomeomorph.apply_symm_apply q)
  change spinorQuaternion (unitSpinorQuaternionHomeomorph.symm q).1 = q.1 at he
  change (fun j => -(spinorQuadratic (unitSpinorQuaternionHomeomorph.symm q).1 j).im) = _
  rw [← spinorQuaternion_axisJ,he]

theorem unitQuaternionFrame_isCoveringMap : IsCoveringMap unitQuaternionFrame :=
  unitSpinorTangentFrame_isCoveringMap.comp_homeomorph unitSpinorQuaternionHomeomorph.symm

theorem unitQuaternionFrame_spinor (s : UnitSpinor) :
    unitQuaternionFrame (unitSpinorQuaternionHomeomorph s) = unitSpinorTangentFrame s := by
  simp [unitQuaternionFrame]

theorem unitQuaternionFrame_fibers {q r : UnitQuaternion} :
    unitQuaternionFrame q = unitQuaternionFrame r ↔ q.1 = r.1 ∨ q.1 = -r.1 := by
  have hr := congrArg Subtype.val (unitSpinorQuaternionHomeomorph.apply_symm_apply r)
  change spinorQuaternionLinearEquiv (unitSpinorQuaternionHomeomorph.symm r).1 = r.1 at hr
  rw [unitQuaternionFrame,Function.comp_apply,Function.comp_apply,unitSpinorTangentFrame_fibers]
  constructor
  · rintro (he | he)
    · exact Or.inl (congrArg Subtype.val (unitSpinorQuaternionHomeomorph.symm.injective he))
    · right
      have hh := congrArg (fun s : UnitSpinor => spinorQuaternion s.1) he
      change (unitSpinorQuaternionHomeomorph (unitSpinorQuaternionHomeomorph.symm q)).1 =
        spinorQuaternion (-(unitSpinorQuaternionHomeomorph.symm r).1) at hh
      change _ = -r.1
      rw [unitSpinorQuaternionHomeomorph.apply_symm_apply] at hh
      change q.1 = spinorQuaternionLinearEquiv (-(unitSpinorQuaternionHomeomorph.symm r).1) at hh
      rw [map_neg] at hh
      rw [hr] at hh
      exact hh
  · rintro (he | he)
    · exact Or.inl (congrArg unitSpinorQuaternionHomeomorph.symm (Subtype.ext he))
    · right
      apply unitSpinorQuaternionHomeomorph.injective
      rw [unitSpinorQuaternionHomeomorph.apply_symm_apply]
      apply Subtype.ext
      change q.1 = spinorQuaternion (-(unitSpinorQuaternionHomeomorph.symm r).1)
      change q.1 = spinorQuaternionLinearEquiv (-(unitSpinorQuaternionHomeomorph.symm r).1)
      rw [map_neg,hr]
      exact he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unitQuaternionFrame_isCoveringMap
#print axioms TwoAxisHelicoid.unitQuaternionFrame_fibers
