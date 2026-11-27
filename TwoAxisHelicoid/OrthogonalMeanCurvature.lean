import TwoAxisHelicoid.MeanCurvatureNumerator
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Equiv

namespace TwoAxisHelicoid
open Complex Matrix
open scoped Matrix

/-- Under an ambient linear change of coordinates every scalar triple
product picks up the same determinant, including orientation reversal. -/
theorem spatial_triple_product_map (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (u v w : Fin 3 → ℝ) :
    L u ⬝ᵥ (L v ⨯₃ L w) = (u ⬝ᵥ (v ⨯₃ w)) * (LinearMap.toMatrix' L).det := by
  have rows : Matrix.of ![u,v,w] * (LinearMap.toMatrix' L)ᵀ =
      Matrix.of ![L u,L v,L w] := by
    funext i
    rw [mul_apply_eq_vecMul,vecMul_transpose,LinearMap.toMatrix'_mulVec]
    fin_cases i <;> rfl
  rw [triple_product_eq_det,triple_product_eq_det]
  change (Matrix.of ![L u,L v,L w]).det=(Matrix.of ![u,v,w]).det*(LinearMap.toMatrix' L).det
  rw [← rows,det_mul,det_transpose]

/-- Moving a surface by any Euclidean rigid motion preserves the zero of
its scalar mean curvature in its original smooth surface chart. -/
theorem coordinate_minimal_orthogonal_affine {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (L : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)) (orth : ∀ u v, L u ⬝ᵥ L v = u ⬝ᵥ v)
    (o : Fin 3 → ℝ) (minimal : coordinateMeanCurvature X z = 0) :
    coordinateMeanCurvature (fun w => o+L (X w)) z = 0 := by
  let Y := fun w => o+L (X w)
  have first : fderiv ℝ Y = fun w => L.toContinuousLinearMap.comp (fderiv ℝ X w) := by
    funext w
    rw [show fderiv ℝ Y w = fderiv ℝ (L ∘ X) w from fderiv_const_add o,L.comp_fderiv]
  have second (u v : ℂ) : fderiv ℝ (fderiv ℝ Y) z u v = L (fderiv ℝ (fderiv ℝ X) z u v) := by
    rw [first,fderiv_continuousLinearEquiv_comp]
    rfl
  have firstAt (u : ℂ) : fderiv ℝ Y z u = L (fderiv ℝ X z u) := by rw [first]; rfl
  change coordinateMeanCurvature Y z=0
  rw [coordinateMeanCurvature_zero_iff_numerator] at minimal ⊢
  simp only [second,firstAt,meanCurvatureNumerator,orth] at *
  have triple (u v w : Fin 3 → ℝ) : L u ⬝ᵥ (L v ⨯₃ L w) =
      (u ⬝ᵥ (v ⨯₃ w)) * (LinearMap.toMatrix' L.toLinearEquiv.toLinearMap).det :=
    spatial_triple_product_map L.toLinearEquiv.toLinearMap u v w
  simp only [triple]
  linear_combination (LinearMap.toMatrix' L.toLinearEquiv.toLinearMap).det * minimal

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coordinate_minimal_orthogonal_affine
