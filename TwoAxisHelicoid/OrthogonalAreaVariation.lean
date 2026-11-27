import TwoAxisHelicoid.CoordinateAreaHessian
import Mathlib.Analysis.Calculus.FDeriv.Equiv

namespace TwoAxisHelicoid
open Complex Matrix

/-- The coordinate area of any global variation is unchanged by a fixed
orthogonal Euclidean frame. The equality also holds at points where a
directional derivative is represented by the default zero value. -/
theorem coordinate_area_orthogonal_affine (T : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ))
    (hT : ∀ a b, T a ⬝ᵥ T b = a ⬝ᵥ b) (v : Fin 3 → ℝ) (X : ℂ → Fin 3 → ℝ) (z : ℂ) :
    coordinateAreaDensity (fun w => v+T (X w)) z = coordinateAreaDensity X z := by
  have hd (g : ℝ → Fin 3 → ℝ) : deriv (fun t => v+T (g t)) 0 = T (deriv g 0) := by
    rw [deriv_const_add]
    change fderiv ℝ (T ∘ g) 0 1 = T (fderiv ℝ g 0 1)
    rw [T.comp_fderiv]
    rfl
  unfold coordinateAreaDensity
  rw [hd (fun t : ℝ => X (z+(t:ℂ))),hd (fun t : ℝ => X (z+I*(t:ℂ)))]
  simp only [hT]

theorem orthogonal_affine_normal_variation {M : Type*} (T : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ))
    (v : Fin 3 → ℝ) (X N : M → Fin 3 → ℝ) (u : M → ℝ) (s : ℝ) (x : M) :
    v+T (X x+s • (u x • T.symm (N x))) = (v+T (X x))+s • (u x • N x) := by
  rw [map_add,map_smul,map_smul,T.apply_symm_apply,add_assoc]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.coordinate_area_orthogonal_affine
