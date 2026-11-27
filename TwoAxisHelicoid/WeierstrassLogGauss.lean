import TwoAxisHelicoid.LogGaussEnergy
import TwoAxisHelicoid.WeierstrassRotation

namespace TwoAxisHelicoid
open Complex

/-- The actual real tangent vectors of the height-normalized Weierstrass
representation when the Gauss map is exp W. -/
noncomputable def logGaussTangentX (u v : ℝ) : Fin 3 → ℝ :=
  ![-Real.sinh u*Real.cos v,-Real.sinh u*Real.sin v,1]

noncomputable def logGaussTangentY (u v : ℝ) : Fin 3 → ℝ :=
  ![Real.cosh u*Real.sin v,-Real.cosh u*Real.cos v,0]

theorem weierstrassTriple_exp (z : ℂ) :
    weierstrassTriple (exp z) 1 = ![-sinh z,I*cosh z,1] := by
  ext j
  fin_cases j <;> dsimp [weierstrassTriple]
  · rw [Complex.sinh,exp_neg]
    ring
  · rw [Complex.cosh,exp_neg]
    ring

theorem complex_sinh_re_im_formula (z : ℂ) :
    (sinh z).re = Real.sinh z.re*Real.cos z.im ∧
    (sinh z).im = Real.cosh z.re*Real.sin z.im := by
  have he : sinh z = (Real.sinh z.re : ℂ)*(Real.cos z.im : ℂ)+
      (Real.cosh z.re : ℂ)*(Real.sin z.im : ℂ)*I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [sinh_add,cosh_mul_I,sinh_mul_I,← ofReal_sinh,← ofReal_cosh,
      ← ofReal_sin,← ofReal_cos]
    ring
  rw [he]
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,zero_mul,mul_zero,mul_one,
    sub_zero,zero_add,add_zero,and_self]

theorem complex_cosh_re_im_formula (z : ℂ) :
    (cosh z).re = Real.cosh z.re*Real.cos z.im ∧
    (cosh z).im = Real.sinh z.re*Real.sin z.im := by
  have he : cosh z = (Real.cosh z.re : ℂ)*(Real.cos z.im : ℂ)+
      (Real.sinh z.re : ℂ)*(Real.sin z.im : ℂ)*I := by
    conv_lhs => rw [← Complex.re_add_im z]
    rw [cosh_add,cosh_mul_I,sinh_mul_I,← ofReal_sinh,← ofReal_cosh,
      ← ofReal_sin,← ofReal_cos]
    ring
  rw [he]
  simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,zero_mul,mul_zero,mul_one,
    sub_zero,zero_add,add_zero,and_self]

theorem weierstrass_exp_real_tangents (z : ℂ) :
    nullRealDerivative (weierstrassTriple (exp z) 1) 1 = logGaussTangentX z.re z.im ∧
    nullRealDerivative (weierstrassTriple (exp z) 1) I = logGaussTangentY z.re z.im := by
  rw [weierstrassTriple_exp]
  obtain ⟨hsr,hsi⟩ := complex_sinh_re_im_formula z
  obtain ⟨hcr,hci⟩ := complex_cosh_re_im_formula z
  constructor <;> ext j <;> fin_cases j <;>
    simp [logGaussTangentX,logGaussTangentY,Complex.mul_re,Complex.mul_im,hsr,hsi,hcr,hci]

theorem logGaussTangent_conformal (u v : ℝ) :
    (∑ j, (logGaussTangentX u v j)^2) = (Real.cosh u)^2 ∧
    (∑ j, (logGaussTangentY u v j)^2) = (Real.cosh u)^2 ∧
    (∑ j, logGaussTangentX u v j*logGaussTangentY u v j) = 0 := by
  simp only [Fin.sum_univ_succ,logGaussTangentX,logGaussTangentY,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
  constructor
  · nlinarith [Real.cosh_sq_sub_sinh_sq u,
      congrArg (fun x : ℝ => (Real.sinh u)^2*x) (Real.sin_sq_add_cos_sq v)]
  constructor
  · nlinarith [congrArg (fun x : ℝ => (Real.cosh u)^2*x) (Real.sin_sq_add_cos_sq v)]
  · ring

theorem logGaussSphere_normal_to_tangents (u v : ℝ) :
    (∑ j, logGaussSphere u v j*logGaussTangentX u v j) = 0 ∧
    (∑ j, logGaussSphere u v j*logGaussTangentY u v j) = 0 := by
  simp only [Fin.sum_univ_succ,logGaussSphere,logGaussTangentX,logGaussTangentY,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero]
  constructor
  · field_simp [(Real.cosh_pos u).ne']
    nlinarith [congrArg (fun x : ℝ => Real.sinh u*x) (Real.sin_sq_add_cos_sq v)]
  · field_simp [(Real.cosh_pos u).ne']
    ring

/-- The sphere-valued map used in the end-potential calculation is a unit
normal to the actual height-normalized Weierstrass derivative. -/
theorem holomorphicLogGaussNormal_actual_weierstrass_normal
    (W : ℂ → ℂ) (z : ℂ) :
    (∑ j, (holomorphicLogGaussNormal W z j)^2) = 1 ∧
    (∑ j, holomorphicLogGaussNormal W z j*
      nullRealDerivative (weierstrassTriple (exp (W z)) 1) 1 j) = 0 ∧
    (∑ j, holomorphicLogGaussNormal W z j*
      nullRealDerivative (weierstrassTriple (exp (W z)) 1) I j) = 0 := by
  obtain ⟨hx,hy⟩ := weierstrass_exp_real_tangents (W z)
  rw [hx,hy]
  exact ⟨logGaussSphere_unit _ _,logGaussSphere_normal_to_tangents _ _⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.holomorphicLogGaussNormal_actual_weierstrass_normal
