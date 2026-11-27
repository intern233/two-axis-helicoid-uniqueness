import TwoAxisHelicoid.NormalVariationFrame
import TwoAxisHelicoid.WeierstrassSecondForm

set_option autoImplicit false
namespace TwoAxisHelicoid
open Matrix Complex

noncomputable def logGaussNormalX (u v : ℝ) (D : ℂ) : Fin 3 → ℝ :=
  D.re • logGaussSphereU u v+D.im • logGaussSphereV u v
noncomputable def logGaussNormalY (u v : ℝ) (D : ℂ) : Fin 3 → ℝ :=
  -D.im • logGaussSphereU u v+D.re • logGaussSphereV u v

theorem logGaussSphere_orthogonal_derivatives (u v : ℝ) :
    logGaussSphere u v ⬝ᵥ logGaussSphereU u v = 0 ∧
    logGaussSphere u v ⬝ᵥ logGaussSphereV u v = 0 := by
  simp only [dotProduct,Fin.sum_univ_succ,logGaussSphere,logGaussSphereU,logGaussSphereV,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
  constructor
  · field_simp [(Real.cosh_pos u).ne']
    nlinarith [congrArg (fun x : ℝ => Real.sinh u*x) (Real.sin_sq_add_cos_sq v)]
  · ring

theorem logGauss_conformal_normal_frame (u v : ℝ) (D : ℂ) :
    ConformalNormalFrame (logGaussTangentX u v) (logGaussTangentY u v)
      (logGaussSphere u v) (logGaussNormalX u v D) (logGaussNormalY u v D)
      ((Real.cosh u)^2) (-D.re) D.im := by
  obtain ⟨hA,hB,hAB⟩ := logGaussTangent_conformal u v
  obtain ⟨hNA,hNB⟩ := logGaussSphere_normal_to_tangents u v
  obtain ⟨hUU,hVV,hUV⟩ := logGaussSphere_frame_metric u v
  have hU : logGaussSphereU u v ⬝ᵥ logGaussSphereU u v = 1/(Real.cosh u)^2 := by
    simpa only [dotProduct,pow_two] using hUU
  have hV : logGaussSphereV u v ⬝ᵥ logGaussSphereV u v = 1/(Real.cosh u)^2 := by
    simpa only [dotProduct,pow_two] using hVV
  have hUVdot : logGaussSphereU u v ⬝ᵥ logGaussSphereV u v = 0 := hUV
  have hVU : logGaussSphereV u v ⬝ᵥ logGaussSphereU u v = 0 :=
    (dotProduct_comm _ _).trans hUV
  obtain ⟨hNU,hNV⟩ := logGaussSphere_orthogonal_derivatives u v
  obtain ⟨hUA,hVA,hUB,hVB⟩ := logGauss_frame_tangent_pairings u v
  refine {
    metric_pos := sq_pos_of_pos (Real.cosh_pos u)
    aa := by simpa only [dotProduct,pow_two] using hA
    bb := by simpa only [dotProduct,pow_two] using hB
    ab := hAB
    nn := by simpa only [dotProduct,pow_two] using logGaussSphere_unit u v
    na := hNA
    nb := hNB
    nnx := ?_
    nny := ?_
    nxnx := ?_
    nyny := ?_
    nxny := ?_
    nxa := ?_
    nxb := ?_
    nya := ?_
    nyb := ?_ }
  all_goals
    simp only [logGaussNormalX,logGaussNormalY,add_dotProduct,dotProduct_add,
      smul_dotProduct,dotProduct_smul,smul_eq_mul,hU,hV,hUVdot,hVU,hNU,hNV,hUA,hVA,hUB,hVB]
    ring

/-- The pointwise second variation for actual Weierstrass tangents and
actual derivatives of their unit Gauss normal. -/
theorem weierstrass_vector_normal_area_second_variation
    {W : ℂ → ℂ} {D z : ℂ} (hW : HasDerivAt W D z) (u ux uy : ℝ) :
    HasDerivAt (deriv (vectorNormalVariationArea
      (nullRealDerivative (weierstrassTriple (exp (W z)) 1) 1)
      (nullRealDerivative (weierstrassTriple (exp (W z)) 1) I)
      (holomorphicLogGaussNormal W z)
      (deriv (fun s : ℝ => holomorphicLogGaussNormal W (z+(s : ℂ))) 0)
      (deriv (fun s : ℝ => holomorphicLogGaussNormal W (z+I*(s : ℂ))) 0)
      u ux uy)) (ux^2+uy^2-(2*‖D‖^2/(Real.cosh (W z).re)^2)*u^2) 0 := by
  obtain ⟨hA,hB⟩ := weierstrass_exp_real_tangents (W z)
  have hnx : deriv (fun s : ℝ => holomorphicLogGaussNormal W (z+(s : ℂ))) 0 =
      logGaussNormalX (W z).re (W z).im D := by
    simpa only [mul_one,one_mul,logGaussNormalX] using
      (holomorphicLogGaussNormal_line_hasDerivAt hW 1).deriv
  have hny : deriv (fun s : ℝ => holomorphicLogGaussNormal W (z+I*(s : ℂ))) 0 =
      logGaussNormalY (W z).re (W z).im D := by
    simpa [logGaussNormalY,Complex.mul_re,Complex.mul_im,mul_comm (I : ℂ)] using
      (holomorphicLogGaussNormal_line_hasDerivAt hW I).deriv
  rw [hA,hB,hnx,hny]
  have hn : (-D.re)^2+D.im^2 = ‖D‖^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply]
    ring
  have h := vector_normal_area_second_variation (logGauss_conformal_normal_frame
    (W z).re (W z).im D) u ux uy
  rw [hn] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrass_vector_normal_area_second_variation
