import TwoAxisHelicoid.TorusGaussFluxRigidity

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate

/-- Recover the Gauss multiplier from a rotation of the spatial differential.
The formula applies simultaneously at ordinary and vertical tangent planes. -/
theorem nullGauss_of_rotated_real_derivative {p q : Fin 3 → ℂ} {c : ℂ} (hc : ‖c‖ = 1)
    (h : nullRealDerivative q = (verticalRotation c).comp (nullRealDerivative p)) :
    nullGauss q = c*nullGauss p := by
  have hv (w : ℂ) (j : Fin 3) := congrArg (fun f : ℂ →L[ℝ] (Fin 3 → ℝ) => f w j) h
  have row (j : Fin 3) : q j = ![(c.re:ℂ)*p 0-(c.im:ℂ)*p 1,
      (c.im:ℂ)*p 0+(c.re:ℂ)*p 1,p 2] j := by
    have hr := hv 1 j
    have hi := hv I j
    fin_cases j <;> apply Complex.ext <;>
      simp [Complex.mul_re,Complex.mul_im] at hr hi ⊢ <;> linarith
  have e : nullHorizontalMinus q = conj c*nullHorizontalMinus p := by
    rw [nullHorizontalMinus,nullHorizontalMinus,row 0,row 1]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
  rw [← Complex.inv_eq_conj hc] at e
  unfold nullGauss
  rw [e,row 2]
  simp [div_eq_mul_inv,mul_comm]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.nullGauss_of_rotated_real_derivative
