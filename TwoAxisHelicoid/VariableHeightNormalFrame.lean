import TwoAxisHelicoid.HeightNormalAreaFormula

namespace TwoAxisHelicoid
open Complex Matrix

/-- Multiplying the Weierstrass height differential by a nonzero
complex number changes the tangent basis conformally. The quotient of
squared second form coefficients by the metric coefficient is invariant. -/
theorem ConformalNormalFrame.change_height {A B N nx ny : Fin 3 → ℝ} {g b c : ℝ}
    (f : ConformalNormalFrame A B N nx ny g b c) (u v : ℝ) (positive : 0<u^2+v^2) :
    ConformalNormalFrame (u • A+v • B) (-v • A+u • B) N nx ny
      ((u^2+v^2)*g) (u*b+v*c) (-v*b+u*c) := by
  have ba : B ⬝ᵥ A=0 := (dotProduct_comm _ _).trans f.ab
  have energy : ((u*b+v*c)^2+(-v*b+u*c)^2)/((u^2+v^2)*g)=(b^2+c^2)/g := by
    rw [show (u*b+v*c)^2+(-v*b+u*c)^2=(u^2+v^2)*(b^2+c^2) by ring]
    field_simp [positive.ne',f.metric_pos.ne']
  refine ⟨mul_pos positive f.metric_pos,?_,?_,?_,f.nn,?_,?_,f.nnx,f.nny,
    energy.symm ▸ f.nxnx,energy.symm ▸ f.nyny,f.nxny,?_,?_,?_,?_⟩
  all_goals simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    f.aa,f.bb,f.ab,ba,f.na,f.nb,f.nxa,f.nxb,f.nya,f.nyb]
  all_goals ring

theorem weierstrass_variable_height_tangents (g h : ℂ) :
    let D := nullRealDerivative (weierstrassTriple g 1)
    nullRealDerivative (weierstrassTriple g h) 1=h.re • D 1+h.im • D I ∧
    nullRealDerivative (weierstrassTriple g h) I= -h.im • D 1+h.re • D I := by
  have fac (j : Fin 3) : weierstrassTriple g h j=h*weierstrassTriple g 1 j := by
    fin_cases j <;> simp [weierstrassTriple,mul_comm]
  constructor <;> funext j <;> simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,nullRealDerivative_apply,fac,
    one_mul,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im] <;> ring

/-- The vector frame of a regular Weierstrass chart with arbitrary
height coefficient and holomorphic logarithm of its Gauss map. -/
theorem variable_height_log_gauss_frame (w D h : ℂ) (hn : h≠0) :
    ConformalNormalFrame (nullRealDerivative (weierstrassTriple (exp w) h) 1)
      (nullRealDerivative (weierstrassTriple (exp w) h) I) (logGaussSphere w.re w.im)
      (logGaussNormalX w.re w.im D) (logGaussNormalY w.re w.im D)
      (‖h‖^2*(Real.cosh w.re)^2) (h.re*(-D.re)+h.im*D.im) (-h.im*(-D.re)+h.re*D.im) := by
  have sq : h.re^2+h.im^2=‖h‖^2 := (by simpa [Complex.normSq_apply,pow_two] using Complex.normSq_eq_norm_sq h)
  obtain ⟨a,b⟩ := weierstrass_variable_height_tangents (exp w) h
  obtain ⟨x,y⟩ := weierstrass_exp_real_tangents w
  rw [a,b,x,y,← sq]
  exact (logGauss_conformal_normal_frame w.re w.im D).change_height h.re h.im (sq.symm ▸ sq_pos_of_pos (norm_pos_iff.mpr hn))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.variable_height_log_gauss_frame
