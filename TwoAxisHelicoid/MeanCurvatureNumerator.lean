import TwoAxisHelicoid.GraphMeanCurvature
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology ContDiff
set_option maxHeartbeats 1300000

/-- Clearing the first fundamental form and the normal normalization gives
a polynomial criterion for zero mean curvature. -/
def meanCurvatureNumerator (A B C D E : Fin 3 → ℝ) : ℝ :=
  (B ⬝ᵥ B)*(C ⬝ᵥ (A ⨯₃ B)) - 2*(A ⬝ᵥ B)*(D ⬝ᵥ (A ⨯₃ B)) +
    (A ⬝ᵥ A)*(E ⬝ᵥ (A ⨯₃ B))

theorem coordinateMeanCurvature_zero_iff_numerator (X : ℂ → Fin 3 → ℝ) (z : ℂ) :
    coordinateMeanCurvature X z = 0 ↔
      meanCurvatureNumerator (fderiv ℝ X z 1) (fderiv ℝ X z I)
        (fderiv ℝ (fderiv ℝ X) z 1 1) (fderiv ℝ (fderiv ℝ X) z 1 I)
        (fderiv ℝ (fderiv ℝ X) z I I) = 0 := by
  unfold coordinateMeanCurvature
  dsimp only
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  let A := fderiv ℝ X z 1
  let B := fderiv ℝ X z I
  let C := fderiv ℝ (fderiv ℝ X) z 1 1
  let D := fderiv ℝ (fderiv ℝ X) z 1 I
  let E := fderiv ℝ (fderiv ℝ X) z I I
  let N := A ⨯₃ B
  have hN : N ⬝ᵥ N = (A ⬝ᵥ A)*(B ⬝ᵥ B)-(A ⬝ᵥ B)^2 := by
    rw [cross_dot_cross,dotProduct_comm B A,pow_two]
  let W := Real.sqrt (N ⬝ᵥ N)
  change ((B ⬝ᵥ B)*(C ⬝ᵥ (W⁻¹ • N))-2*(A ⬝ᵥ B)*(D ⬝ᵥ (W⁻¹ • N))+
      (A ⬝ᵥ A)*(E ⬝ᵥ (W⁻¹ • N)))/(2*((A ⬝ᵥ A)*(B ⬝ᵥ B)-(A ⬝ᵥ B)^2)) = 0 ↔ meanCurvatureNumerator A B C D E = 0
  rw [← hN]
  by_cases hno : N = 0
  · simp [hno,meanCurvatureNumerator,show A ⨯₃ B = 0 from hno]
  · have hpos : 0 < N ⬝ᵥ N := lt_of_le_of_ne
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg _)) (fun he => hno (dotProduct_self_eq_zero.mp he.symm))
    have hw : W ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    rw [div_eq_zero_iff,or_iff_left (mul_ne_zero two_ne_zero hpos.ne')]
    simp only [dotProduct_smul,smul_eq_mul]
    have he : (B ⬝ᵥ B)*(W⁻¹*(C ⬝ᵥ N))-2*(A ⬝ᵥ B)*(W⁻¹*(D ⬝ᵥ N))+
        (A ⬝ᵥ A)*(W⁻¹*(E ⬝ᵥ N)) = W⁻¹*meanCurvatureNumerator A B C D E := by
      unfold meanCurvatureNumerator
      dsimp only [N]
      ring
    rw [he,mul_eq_zero,or_iff_right (inv_ne_zero hw)]

theorem cross_product_two_basis_changes (A B : Fin 3 → ℝ) (a b c d : ℝ) :
    (a • A+b • B) ⨯₃ (c • A+d • B) = (a*d-b*c) • (A ⨯₃ B) := by
  ext i
  fin_cases i <;> simp [cross_apply] <;> ring

theorem meanCurvatureNumerator_basis_change (A B C D E : Fin 3 → ℝ) (a b c d : ℝ)
    (r s t u v w : ℝ) :
    meanCurvatureNumerator (a • A+b • B) (c • A+d • B)
      (a^2 • C+(2*a*b) • D+b^2 • E+r • A+s • B)
      ((a*c) • C+(a*d+b*c) • D+(b*d) • E+t • A+u • B)
      (c^2 • C+(2*c*d) • D+d^2 • E+v • A+w • B) =
    (a*d-b*c)^3 * meanCurvatureNumerator A B C D E := by
  simp only [meanCurvatureNumerator,cross_product_two_basis_changes,add_dotProduct,dotProduct_add,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,dot_self_cross,dot_cross_self,mul_zero,add_zero]
  rw [dotProduct_comm B A]
  ring

theorem surface_composition_second_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : ℂ → E} {f : ℂ → ℂ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X (f z)) (hf : ContDiffAt ℝ 2 f z) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (X ∘ f)) z v w =
      fderiv ℝ X (f z) (fderiv ℝ (fderiv ℝ f) z v w) +
      fderiv ℝ (fderiv ℝ X) (f z) (fderiv ℝ f z v) (fderiv ℝ f z w) := by
  have hX' := (hX.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hf' := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hx := hX'.hasFDerivAt.comp z (hf.differentiableAt two_ne_zero).hasFDerivAt
  have he : fderiv ℝ (X ∘ f) =ᶠ[𝓝 z] fun w => ((fderiv ℝ X ∘ f) w).comp (fderiv ℝ f w) := by
    filter_upwards [hf.eventually (by norm_num),hf.continuousAt.eventually (hX.eventually (by norm_num))]
      with y hy hxy
    exact fderiv_comp y (hxy.differentiableAt two_ne_zero) (hy.differentiableAt two_ne_zero)
  rw [he.fderiv_eq,(hx.clm_comp hf'.hasFDerivAt).fderiv]
  rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.coordinateMeanCurvature_zero_iff_numerator
