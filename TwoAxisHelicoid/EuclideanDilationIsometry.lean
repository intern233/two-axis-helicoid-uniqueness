import Mathlib.Analysis.Normed.Affine.AddTorsor

namespace TwoAxisHelicoid

/-- On real normed spaces a surjective dilation is exactly a strictly
positive scalar followed by a surjective metric isometry. Its isometry
can reverse orientation. -/
theorem dilation_eq_positive_smul_isometry {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E ≃ᵈ F) :
    ∃ (k : ℝ) (T : E ≃ᵢ F), 0 < k ∧ ∀ x, f x = k • T x := by
  let k : ℝ := Dilation.ratio f
  have hk : 0 < k := Dilation.ratio_pos f
  let e := f.toEquiv.trans (DilationEquiv.smulTorsor (0:F) (inv_ne_zero hk.ne')).toEquiv
  have h (x : E) : e x = k⁻¹ • f x := by change k⁻¹ • f x+0 = _; simp
  let T : E ≃ᵢ F := {
    toEquiv := e
    isometry_toFun := Isometry.of_dist_eq (fun x y => by
      change dist (e x) (e y) = _
      rw [h,h,dist_eq_norm,← smul_sub,norm_smul,← dist_eq_norm,Dilation.dist_eq]
      change ‖k⁻¹‖*(k*_) = _
      rw [Real.norm_of_nonneg (inv_pos.mpr hk).le,← mul_assoc,inv_mul_cancel₀ hk.ne',one_mul]) }
  refine ⟨k,T,hk,fun x => ?_⟩
  change f x = k • e x
  rw [h,smul_inv_smul₀ hk.ne']

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.dilation_eq_positive_smul_isometry
