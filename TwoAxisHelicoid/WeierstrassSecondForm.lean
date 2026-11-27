import TwoAxisHelicoid.WeierstrassLogGauss

set_option autoImplicit false
namespace TwoAxisHelicoid
open Complex Matrix

theorem logGauss_frame_tangent_pairings (u v : ℝ) :
    logGaussSphereU u v ⬝ᵥ logGaussTangentX u v = 1 ∧
    logGaussSphereV u v ⬝ᵥ logGaussTangentX u v = 0 ∧
    logGaussSphereU u v ⬝ᵥ logGaussTangentY u v = 0 ∧
    logGaussSphereV u v ⬝ᵥ logGaussTangentY u v = -1 := by
  simp only [dotProduct,Fin.sum_univ_succ,logGaussSphereU,logGaussSphereV,
    logGaussTangentX,logGaussTangentY,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero]
  constructor
  · field_simp [(Real.cosh_pos u).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq u,
      congrArg (fun x : ℝ => (Real.sinh u)^2*x) (Real.sin_sq_add_cos_sq v)]
  constructor
  · ring
  constructor
  · ring
  · field_simp [(Real.cosh_pos u).ne']
    nlinarith [Real.sin_sq_add_cos_sq v]

/-- The second fundamental coefficients computed from the derivatives of
the actual unit normal and the actual Weierstrass tangent vectors. -/
noncomputable def logGaussSecondForm (W : ℂ → ℂ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => -(deriv (fun s : ℝ => holomorphicLogGaussNormal W (z+(s : ℂ)*![1,I] i)) 0
    ⬝ᵥ nullRealDerivative (weierstrassTriple (exp (W z)) 1) (![1,I] j))

theorem logGaussSecondForm_formula {W : ℂ → ℂ} {D z : ℂ} (hW : HasDerivAt W D z) :
    logGaussSecondForm W z = !![-D.re,D.im;D.im,D.re] := by
  have hx := (holomorphicLogGaussNormal_line_hasDerivAt hW 1).deriv
  have hy := (holomorphicLogGaussNormal_line_hasDerivAt hW I).deriv
  obtain ⟨htx,hty⟩ := weierstrass_exp_real_tangents (W z)
  obtain ⟨hux,hvx,huy,hvy⟩ := logGauss_frame_tangent_pairings (W z).re (W z).im
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp [logGaussSecondForm] <;>
    simp only [hx,hy,htx,hty,add_dotProduct,smul_dotProduct,hux,hvx,huy,hvy,
      smul_eq_mul,one_mul,Complex.I_mul_re,Complex.I_mul_im] <;> ring

/-- Trace zero and the exact squared second-form density with the conformal
area factor included. The metric is cosh(Re W)^2 times the flat metric. -/
theorem logGaussSecondForm_trace_and_density {W : ℂ → ℂ} {D z : ℂ}
    (hW : HasDerivAt W D z) :
    logGaussSecondForm W z 0 0+logGaussSecondForm W z 1 1 = 0 ∧
    ((∑ i : Fin 2, ∑ j : Fin 2, (logGaussSecondForm W z i j)^2)/(Real.cosh (W z).re)^2) =
      2*‖D‖^2/(Real.cosh (W z).re)^2 := by
  rw [logGaussSecondForm_formula hW]
  constructor
  · dsimp; ring
  · simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    dsimp
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply]
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.logGaussSecondForm_trace_and_density
