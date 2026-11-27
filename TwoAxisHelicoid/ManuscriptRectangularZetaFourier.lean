import TwoAxisHelicoid.RectangularProductZeta
import TwoAxisHelicoid.RectangularProductLambert
import TwoAxisHelicoid.RectangularFourierConvergence

namespace TwoAxisHelicoid
open Complex Set Filter Topology

/-- Equation two_axis_helicoid:eq-rectangular-zeta in the original complex
normalization. The series may be differentiated at every point of
the open strip, and converges uniformly on its closed inner strips. -/
theorem manuscript_rectangular_zeta_fourier {t : ℝ} (ht : 0<t) {z : ℂ}
    (inside : |z.im|<2*t) (regular : z∉(manuscriptRectangularLattice t ht).lattice) :
    let R := manuscriptRectangularLattice t ht
    let q : ℂ := Real.exp (-Real.pi*t)
    let T := fun (j : ℕ) (w : ℂ) => q^(2*(j+1))/(1-q^(2*(j+1)))*
      Complex.sin (((j+1:ℕ):ℂ)*Real.pi*w)
    Summable (fun j => T j z) ∧
    markedWeierstrassZeta R z=markedWeierstrassZeta R 1*z+
      (Real.pi:ℂ)/2*Complex.cot ((Real.pi:ℂ)*z/2)+2*Real.pi*(∑' j, T j z) ∧
    (∀ h : ℝ, h<2*t → HasSumUniformlyOn T (fun w => ∑' j, T j w) {w : ℂ | |w.im|≤h}) ∧
    HasSum (fun j : ℕ => q^(2*(j+1))/(1-q^(2*(j+1)))*
      (Complex.cos (((j+1:ℕ):ℂ)*Real.pi*z)*(((j+1:ℕ):ℂ)*Real.pi)))
      (deriv (fun w => ∑' j, T j w) z) := by
  let Q := rectangularProductNome t
  have qn := rectangular_nome_exponential_norm t
  have xn : ‖jacobiExp z‖=Real.exp (-Real.pi*z.im) := by
    unfold jacobiExp
    rw [show I*(Real.pi:ℂ)*z=((Real.pi:ℂ)*z)*I by ring,Complex.norm_exp_mul_I,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,neg_mul]
  have xi : ‖(jacobiExp z)⁻¹‖=Real.exp (Real.pi*z.im) := by rw [norm_inv,xn,neg_mul,Real.exp_neg,inv_inv]
  have X : jacobiExp z≠1 := by
    intro eqn
    apply rectangular_product_regular ht regular
    change Complex.exp _*((1-jacobiExp z)*jacobiFactorProduct Q (jacobiExp z)*jacobiFactorProduct Q (jacobiExp z)⁻¹)=0
    rw [eqn,sub_self,zero_mul,zero_mul,mul_zero]
  have hP : ‖Q‖*‖jacobiExp z‖<1 := by
    dsimp only [Q]
    rw [qn,xn,← Real.exp_add,Real.exp_lt_one_iff]
    nlinarith [mul_pos Real.pi_pos (by linarith [(abs_lt.mp inside).1] : 0<2*t+z.im)]
  have hM : ‖Q‖*‖(jacobiExp z)⁻¹‖<1 := by
    dsimp only [Q]
    rw [qn,xi,← Real.exp_add,Real.exp_lt_one_iff]
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr (abs_lt.mp inside).2)]
  obtain ⟨sm,series⟩ := jacobi_product_log_fourier (rectangular_product_nome_norm ht) X hP hM
  have zeta := rectangular_zeta_eq_product ht regular
  dsimp only at zeta
  rw [series,← add_assoc] at zeta
  have uniform (h : ℝ) (hh : h<2*t) := rectangular_fourier_uniform_on_strip ht hh
  unfold rectangularFourierTerm at uniform
  have derivs := (rectangular_fourier_termwise_derivative ht inside).2
  dsimp only
  simpa only [rectangularFourierTerm,rectangular_product_nome_actual,pow_mul] using
    And.intro sm (And.intro zeta (And.intro uniform derivs))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.manuscript_rectangular_zeta_fourier

