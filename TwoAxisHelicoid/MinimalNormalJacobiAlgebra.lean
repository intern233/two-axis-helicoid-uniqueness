import TwoAxisHelicoid.ConformalJacobiFrame

namespace TwoAxisHelicoid
open Matrix

/-- Differentiate the two conformal metric identities in one direction.
The resulting pair of columns has vanishing contraction with the
traceless symmetric Weingarten matrix. -/
theorem ConformalNormalFrame.normal_column_contraction {A B n nx ny U V : Fin 3 → ℝ} {g b c : ℝ}
    (H : ConformalNormalFrame A B n nx ny g b c)
    (h1 : U ⬝ᵥ A = V ⬝ᵥ B) (h2 : U ⬝ᵥ B + V ⬝ᵥ A = 0) :
    U ⬝ᵥ nx + V ⬝ᵥ ny = 0 := by
  have hx := congrArg (fun Y => U ⬝ᵥ Y) H.scaled_normal_columns.1
  have hy := congrArg (fun Y => V ⬝ᵥ Y) H.scaled_normal_columns.2
  simp only [dotProduct_smul,dotProduct_add,smul_eq_mul] at hx hy
  apply (mul_eq_zero.mp (show g*(U ⬝ᵥ nx + V ⬝ᵥ ny) = 0 by
    linear_combination hx + hy - b*h1 - c*h2)).resolve_left H.metric_pos.ne'

theorem ConformalNormalFrame.normal_cross_sum {A B n nx ny : Fin 3 → ℝ} {g b c : ℝ}
    (H : ConformalNormalFrame A B n nx ny g b c) : A ⨯₃ nx + B ⨯₃ ny = 0 := by
  have hx := congrArg (crossProduct A) H.scaled_normal_columns.1
  have hy := congrArg (crossProduct B) H.scaled_normal_columns.2
  simp only [map_smul,map_add,cross_self,smul_zero,zero_add,add_zero] at hx hy
  have he : g • (A ⨯₃ nx + B ⨯₃ ny) = (0 : Fin 3 → ℝ) := by
    rw [smul_add,hx,hy,← smul_add]
    rw [cross_anticomm' A B,smul_zero]
  exact (smul_eq_zero.mp he).resolve_left H.metric_pos.ne'

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ConformalNormalFrame.normal_column_contraction
#print axioms TwoAxisHelicoid.ConformalNormalFrame.normal_cross_sum
