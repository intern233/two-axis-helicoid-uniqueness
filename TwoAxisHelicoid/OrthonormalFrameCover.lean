import TwoAxisHelicoid.UnitSpinorFrameCover
import Mathlib.LinearAlgebra.CrossProduct

namespace TwoAxisHelicoid
open Complex Matrix Set
set_option maxHeartbeats 1000000

/-- Two orthonormal real tangent vectors specify an oriented Euclidean
three-frame by adjoining their cross product. -/
abbrev OrthonormalTangentPair :=
  {v : (Fin 3 → ℝ) × (Fin 3 → ℝ) // v.1 ⬝ᵥ v.1 = 1 ∧ v.2 ⬝ᵥ v.2 = 1 ∧ v.1 ⬝ᵥ v.2 = 0}

noncomputable def tangentPairComplexVector (A B : Fin 3 → ℝ) : Fin 3 → ℂ :=
  fun j => (A j : ℂ)-I*(B j : ℂ)

theorem tangentPairComplexVector_unit_null (v : OrthonormalTangentPair) :
    ComplexNull (tangentPairComplexVector v.1.1 v.1.2) ∧
      nullMetric (tangentPairComplexVector v.1.1 v.1.2) = 1 := by
  have hA := v.2.1
  have hB := v.2.2.1
  have hAB := v.2.2.2
  norm_num [dotProduct,Fin.sum_univ_succ] at hA hB hAB
  constructor
  · unfold ComplexNull
    apply Complex.ext
    · norm_num [tangentPairComplexVector,pow_two,Complex.mul_re,Complex.mul_im]
      nlinarith
    · norm_num [tangentPairComplexVector,pow_two,Complex.mul_re,Complex.mul_im]
      nlinarith
  · norm_num [nullMetric,tangentPairComplexVector]
    nlinarith

noncomputable def unitNullToTangentPair (p : UnitNullFrame) : OrthonormalTangentPair := by
  refine ⟨(fun j => (p.1 j).re,fun j => -(p.1 j).im),?_,?_,?_⟩
  · simpa [dotProduct,Fin.sum_univ_succ,nullMetric,pow_two,add_assoc] using p.2.2
  · have hh := (complexNull_real_identities p.2.1).1
    rw [p.2.2] at hh
    simpa [dotProduct,Fin.sum_univ_succ,pow_two,add_assoc] using hh.symm
  · have hh := (complexNull_real_identities p.2.1).2
    simpa [dotProduct,Fin.sum_univ_succ,add_assoc] using congrArg Neg.neg hh

noncomputable def unitNullTangentPairHomeomorph : UnitNullFrame ≃ₜ OrthonormalTangentPair where
  toFun := unitNullToTangentPair
  invFun v := ⟨tangentPairComplexVector v.1.1 v.1.2,tangentPairComplexVector_unit_null v⟩
  left_inv p := by
    apply Subtype.ext
    funext j
    apply Complex.ext <;> simp [unitNullToTangentPair,tangentPairComplexVector]
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext <;> funext j <;> simp [unitNullToTangentPair,tangentPairComplexVector]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply continuous_pi
      intro j
      exact Complex.continuous_re.comp ((continuous_apply j).comp continuous_subtype_val)
    · apply continuous_pi
      intro j
      exact (Complex.continuous_im.comp ((continuous_apply j).comp continuous_subtype_val)).neg
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    change Continuous (fun v : OrthonormalTangentPair => (v.1.1 j : ℂ)-I*(v.1.2 j : ℂ))
    fun_prop

noncomputable def unitSpinorTangentFrame : UnitSpinor → OrthonormalTangentPair :=
  unitNullTangentPairHomeomorph ∘ unitSpinorQuadratic

/-- An actual twofold covering of oriented orthonormal Euclidean frames,
with the sign ambiguity of the Weierstrass spinor as its deck action. -/
theorem unitSpinorTangentFrame_isCoveringMap : IsCoveringMap unitSpinorTangentFrame :=
  unitSpinorQuadratic_isCoveringMap.homeomorph_comp unitNullTangentPairHomeomorph

theorem unitSpinorTangentFrame_fibers {s t : UnitSpinor} :
    unitSpinorTangentFrame s = unitSpinorTangentFrame t ↔ s = t ∨ s = unitSpinorAntipode t := by
  change unitNullTangentPairHomeomorph (unitSpinorQuadratic s) =
    unitNullTangentPairHomeomorph (unitSpinorQuadratic t) ↔ _
  rw [unitNullTangentPairHomeomorph.injective.eq_iff,unitSpinorQuadratic_fibers]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unitSpinorTangentFrame_isCoveringMap
