import TwoAxisHelicoid.IsothermalComplexAtlas
import Mathlib.LinearAlgebra.Determinant

namespace TwoAxisHelicoid
open Complex

/-- The analytic area formula and the orientation determinant use
the same real Jacobian in the basis 1,i. -/
theorem complex_real_det_eq (L : ℂ →L[ℝ] ℂ) : L.det = planeRealJacobian L := by
  change L.toLinearMap.det = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI,Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Complex.coe_basisOneI,Complex.coe_basisOneI_repr,planeRealJacobian,mul_comm]

/-- If a reparametrization is conformal for a metric between one
quarter and four times the Euclidean metric (up to scale), its
horizontal directional distortion is at most four. -/
theorem horizontal_distortion_of_conformal_bounds (L : ℂ →L[ℝ] ℂ)
    {m c : ℝ} (hm : 0<m)
    (metric : ∀ v : ℂ, m*‖L v‖^2/4 ≤ c*‖v‖^2 ∧ c*‖v‖^2 ≤ 4*(m*‖L v‖^2)) :
    ‖L 1‖^2 ≤ 4*|L.det| := by
  let p := L 1
  let q := L I
  let A := ‖p‖^2
  let D := planeRealJacobian L
  let B := p.re*q.re+p.im*q.im
  let w : ℂ := ⟨-B,A⟩
  have hA : 0≤A := sq_nonneg _
  change A ≤ 4*|L.det|
  rw [complex_real_det_eq]
  change A ≤ 4*|D|
  rcases eq_or_lt_of_le hA with zero | pos
  · rw [← zero]
    positivity
  have aform : A=p.re^2+p.im^2 := by
    change ‖p‖^2=_
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  have perp : L w = (D:ℂ)*I*p := by
    rw [real_linear_complex_expansion L w]
    change (-B) • p + A • q = (D:ℂ)*I*p
    have dform : D=p.re*q.im-p.im*q.re := rfl
    apply Complex.ext <;> simp [Complex.real_smul,Complex.mul_re,Complex.mul_im] <;>
      rw [aform,dform] <;> dsimp [B] <;> ring
  have ratio : ‖L w‖^2=D^2*A := by
    rw [perp,norm_mul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      mul_pow,sq_abs]
  have wn : A^2≤‖w‖^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    change A^2 ≤ (-B)*(-B)+A*A
    nlinarith [sq_nonneg B]
  have pbound := (metric 1).1
  change m*A/4≤c*‖(1:ℂ)‖^2 at pbound
  rw [norm_one,one_pow,mul_one] at pbound
  have cp : 0≤c := le_trans (by positivity) pbound
  have wbound := (metric w).2
  rw [ratio] at wbound
  have cubic : (m*A)*(A^2) ≤ (m*A)*(16*D^2) := by
    nlinarith [mul_le_mul_of_nonneg_right pbound (sq_nonneg A),mul_le_mul_of_nonneg_left wn cp]
  have sq := (le_of_mul_le_mul_left cubic (mul_pos hm pos))
  apply (sq_le_sq₀ hA (by positivity : 0≤4*|D|)).mp
  rw [mul_pow,sq_abs]
  linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.horizontal_distortion_of_conformal_bounds
