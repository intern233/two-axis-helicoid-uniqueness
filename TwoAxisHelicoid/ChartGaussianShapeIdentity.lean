import TwoAxisHelicoid.ChartSecondFundamentalWeingarten
import TwoAxisHelicoid.DirectionalSpinFrame
import TwoAxisHelicoid.SpatialGramFrames
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace TwoAxisHelicoid
open Complex Matrix Filter Set Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- Gaussian curvature, computed as the ratio of the determinants of the
second and first fundamental forms of the actual parametrization. -/
noncomputable def chartGaussianCurvature (Y : ℂ → Fin 3 → ℝ) (z : ℂ) : ℝ :=
  let A := fderiv ℝ Y z 1
  let B := fderiv ℝ Y z I
  let h := chartScalarSecondFundamentalForm Y z
  (h 1 1*h I I-(h 1 I)^2)/((A ⬝ᵥ A)*(B ⬝ᵥ B)-(A ⬝ᵥ B)^2)

private theorem quadratic_weingarten_norm (E F G L M N a b c d : ℝ)
    (first : E*c+F*d= -(L*a+M*b)) (second : F*c+G*d= -(M*a+N*b))
    (trace : G*L-2*F*M+E*N=0) :
    (E*G-F^2)*(E*c^2+2*F*c*d+G*d^2)=(M^2-L*N)*(E*a^2+2*F*a*b+G*b^2) := calc
  _ = G*(E*c+F*d)^2-2*F*(E*c+F*d)*(F*c+G*d)+E*(F*c+G*d)^2 := by ring
  _ = _ := by
    rw [first,second]
    linear_combination (L*a^2+2*M*a*b+N*b^2)*trace

private theorem curvature_chart_inner (a b : Fin 3 → ℝ) :
    ⟪coordinateToEuclidean a,coordinateToEuclidean b⟫=a ⬝ᵥ b := by
  rw [coordinateToEuclidean_apply,coordinateToEuclidean_apply,EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct_comm]

/-- For a regular minimal surface, the squared length of the derivative
of its unit normal in every tangent direction is minus Gaussian
curvature times the squared induced length of that direction. -/
theorem minimal_chart_gaussian_shape_identity {P : Type*} [TopologicalSpace P]
    {X : P → Fin 3 → ℝ} {e : OpenPartialHomeomorph P ℂ} (reg : RegularImmersionChart X e)
    {z : ℂ} (hz : z∈e.target) (minimal : coordinateMeanCurvature (X ∘ e.symm) z=0) (v : ℂ) :
    ‖fderiv ℝ (euclideanUnitChartNormal (X ∘ e.symm)) z v‖^2 =
      -chartGaussianCurvature (X ∘ e.symm) z*‖coordinateToEuclidean (fderiv ℝ (X ∘ e.symm) z v)‖^2 := by
  let Y := X ∘ e.symm
  let D := fderiv ℝ Y z
  let Q := fderiv ℝ (fderiv ℝ Y) z
  let A := D 1
  let B := D I
  let E := A ⬝ᵥ A
  let F := A ⬝ᵥ B
  let G := B ⬝ᵥ B
  let H := chartScalarSecondFundamentalForm Y z
  let L := H 1 1
  let M := H 1 I
  let N := H I I
  have ba : B ⬝ᵥ A=F := dotProduct_comm B A
  have det : 0<E*G-F^2 := by
    have h := spatial_dot_self_pos (surfaceTangentCross_ne_zero_of_injective (reg z hz).2)
    change 0<(A ⨯₃ B) ⬝ᵥ (A ⨯₃ B) at h
    rwa [cross_dot_cross,ba,← pow_two] at h
  have trace : G*L-2*F*M+E*N=0 := by
    change (G*L-2*F*M+E*N)/(2*(E*G-F^2))=0 at minimal
    exact (div_eq_zero_iff.mp minimal).resolve_right (mul_ne_zero two_ne_zero det.ne')
  have hq (w t : ℂ) : H w t=Q w t ⬝ᵥ unitCrossNormal A B := by
    unfold H chartScalarSecondFundamentalForm
    rw [iteratedFDeriv_two_apply]
    rfl
  have symm : H I 1 = M := by
    rw [show M=H 1 I from rfl,hq,hq]
    exact congrArg (fun a => a ⬝ᵥ unitCrossNormal A B) (((reg z hz).1.isSymmSndFDerivAt (by simp)) I 1)
  have hlin (w t : ℂ) : H w t=w.re*H 1 t+w.im*H I t := by
    simp only [hq]
    rw [real_linear_complex_expansion Q w]
    change (w.re • Q 1 t+w.im • Q I t) ⬝ᵥ unitCrossNormal A B=_
    rw [add_dotProduct,smul_dotProduct,smul_dotProduct]
    rfl
  have dp (u : ℂ) : D u=u.re • A+u.im • B := real_linear_complex_expansion D u
  have normForm (u : ℂ) : ‖coordinateToEuclidean (D u)‖^2=E*u.re^2+2*F*u.re*u.im+G*u.im^2 := by
    rw [← real_inner_self_eq_norm_sq,curvature_chart_inner,dp]
    simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,ba]
    dsimp only [E,F,G]
    ring
  obtain ⟨w,hw⟩ := euclidean_normal_derivative_is_tangent reg hz v
  change coordinateToEuclidean (D w)=fderiv ℝ (euclideanUnitChartNormal Y) z v at hw
  have wgt (t : ℂ) : H v t= -(D w ⬝ᵥ D t) := by
    have e := chart_second_fundamental_weingarten_identity reg hz v t
    change H v t= -⟪fderiv ℝ (euclideanUnitChartNormal Y) z v,coordinateToEuclidean (D t)⟫ at e
    rwa [← hw,curvature_chart_inner] at e
  have first : E*w.re+F*w.im= -(L*v.re+M*v.im) := by
    have e := wgt 1
    rw [hlin v 1,symm,dp w] at e
    change v.re*L+v.im*M= -((w.re • A+w.im • B) ⬝ᵥ A) at e
    simp only [add_dotProduct,smul_dotProduct,smul_eq_mul,ba] at e
    change v.re*L+v.im*M= -(w.re*E+w.im*F) at e
    linarith
  have second : F*w.re+G*w.im= -(M*v.re+N*v.im) := by
    have e := wgt I
    rw [hlin v I,dp w] at e
    change v.re*M+v.im*N= -((w.re • A+w.im • B) ⬝ᵥ B) at e
    simp only [add_dotProduct,smul_dotProduct,smul_eq_mul] at e
    change v.re*M+v.im*N= -(w.re*F+w.im*G) at e
    linarith
  change ‖fderiv ℝ (euclideanUnitChartNormal Y) z v‖^2= -((L*N-M^2)/(E*G-F^2))*‖coordinateToEuclidean (D v)‖^2
  rw [← hw,normForm,normForm]
  have algebra := quadratic_weingarten_norm E F G L M N v.re v.im w.re w.im first second trace
  field_simp [det.ne']
  linear_combination algebra

theorem minimal_gaussian_bound_implies_shape_bound {P : Type*} [TopologicalSpace P]
    {X : P → Fin 3 → ℝ} {e : OpenPartialHomeomorph P ℂ} (reg : RegularImmersionChart X e)
    {z : ℂ} (hz : z∈e.target) (minimal : coordinateMeanCurvature (X ∘ e.symm) z=0)
    {C : ℝ} (hC : 0≤C) (bound : |chartGaussianCurvature (X ∘ e.symm) z|≤C) (v : ℂ) :
    ‖fderiv ℝ (euclideanUnitChartNormal (X ∘ e.symm)) z v‖ ≤
      Real.sqrt C*‖coordinateToEuclidean (fderiv ℝ (X ∘ e.symm) z v)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [minimal_chart_gaussian_shape_identity reg hz minimal,mul_pow,Real.sq_sqrt hC]
  exact mul_le_mul_of_nonneg_right ((neg_le_abs _).trans bound) (sq_nonneg _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_chart_gaussian_shape_identity
#print axioms TwoAxisHelicoid.minimal_gaussian_bound_implies_shape_bound
