import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

namespace TwoAxisHelicoid
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The tangent part of a fixed ambient vector at a unit normal. Its sign
is independent of the local choice of unit normal. -/
noncomputable def projectedTangentVelocity (u n : E) : E := u-⟪u,n⟫ • n

theorem projectedTangentVelocity_neg (u n : E) :
    projectedTangentVelocity u (-n) = projectedTangentVelocity u n := by
  simp [projectedTangentVelocity]

theorem projectedTangentVelocity_norm_le (u : E) {n : E} (hn : ‖n‖ = 1) :
    ‖projectedTangentVelocity u n‖ ≤ ‖u‖ := by
  have eq : ‖projectedTangentVelocity u n‖^2 = ‖u‖^2-⟪u,n⟫^2 := by
    rw [projectedTangentVelocity,norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,hn,mul_one,sq_abs]
    ring
  nlinarith [norm_nonneg u,sq_nonneg ⟪u,n⟫]

theorem projectedTangentVelocity_orthogonal (u : E) {n : E} (hn : ‖n‖ = 1) :
    ⟪projectedTangentVelocity u n,n⟫ = 0 := by
  rw [projectedTangentVelocity,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hn]
  ring

/-- Along the orbit of projected velocity, the derivative of the normal is
the shape operator applied to the velocity, up to its sign. The displayed
estimate bounds spatial acceleration by twice its norm for an ambient unit
vector. -/
theorem projectedTangentVelocity_derivative_bound {n : ℝ → E} {dn u : E} {t : ℝ}
    (hd : HasDerivAt n dn t) (hu : ‖u‖ = 1) (hn : ‖n t‖ = 1) :
    ∃ a : E, HasDerivAt (fun s => projectedTangentVelocity u (n s)) a t ∧ ‖a‖ ≤ 2*‖dn‖ := by
  let a := -(⟪u,n t⟫ • dn + ⟪u,dn⟫ • n t)
  refine ⟨a,?_,?_⟩
  · have hi : HasDerivAt (fun s => ⟪u,n s⟫) ⟪u,dn⟫ t := by
      simpa only [inner_zero_left,add_zero] using (hasDerivAt_const t u).inner ℝ hd
    have hp : HasDerivAt (fun s => ⟪u,n s⟫ • n s) (⟪u,n t⟫ • dn + ⟪u,dn⟫ • n t) t :=
      HasDerivAt.smul hi hd
    simpa only [projectedTangentVelocity,a,zero_sub] using HasDerivAt.fun_sub (hasDerivAt_const t u) hp
  · have hnorm := norm_add_le (⟪u,n t⟫ • dn) (⟪u,dn⟫ • n t)
    have h₁ := abs_real_inner_le_norm u (n t)
    have h₂ := abs_real_inner_le_norm u dn
    rw [hu,hn,one_mul] at h₁
    rw [hu,one_mul] at h₂
    simp only [a,norm_neg]
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hn,mul_one] at hnorm
    linarith [mul_le_mul_of_nonneg_right h₁ (norm_nonneg dn)]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.projectedTangentVelocity_derivative_bound
