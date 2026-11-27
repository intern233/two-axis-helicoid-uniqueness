import TwoAxisHelicoid.RectangularSublatticeTrace
import TwoAxisHelicoid.JacobiRatioIdentity
import TwoAxisHelicoid.LogDerivativePrincipalParts
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace TwoAxisHelicoid
open Complex Set Filter Topology

/-- For periods 2 and 2it, the Jacobi product uses the square of the
real nome q=exp(-πt) in the manuscript. -/
noncomputable def rectangularProductNome (t : ℝ) : ℂ := jacobiExp (I*(2*t:ℝ))

theorem rectangular_product_nome_actual (t : ℝ) :
    rectangularProductNome t=((Real.exp (-Real.pi*t):ℂ)^2) := by
  unfold rectangularProductNome jacobiExp
  rw [← Complex.ofReal_pow,← Real.exp_nat_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp only [I_sq]
  ring

theorem rectangular_product_nome_norm {t : ℝ} (ht : 0<t) : ‖rectangularProductNome t‖<1 := by
  rw [rectangular_product_nome_actual,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact pow_lt_one₀ (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) ht)) (by decide)

private theorem jacobi_exp_one_even {z : ℂ} (h : jacobiExp z=1) : ∃m : ℤ, z=(m:ℂ)*2 := by
  obtain ⟨m,e⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨m,?_⟩
  apply mul_left_cancel₀ (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
  linear_combination e

theorem rectangular_product_regular {t : ℝ} (ht : 0<t) {z : ℂ}
    (off : z∉(manuscriptRectangularLattice t ht).lattice) :
    jacobiThetaProduct (rectangularProductNome t) z≠0 := by
  let R := manuscriptRectangularLattice t ht
  let p := R.ω₂
  have hp : p=I*(2*t:ℝ) := by simp [p,R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair]
  have hQ : rectangularProductNome t=jacobiExp p := by rw [hp];rfl
  have whole {w : ℂ} (h : jacobiExp w=1) : w∈R.lattice := by
    obtain ⟨m,rfl⟩ := jacobi_exp_one_even h
    exact PeriodPair.mem_lattice.mpr ⟨m,0,by simp [R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair]⟩
  have sumexp (n : ℕ) (w : ℂ) :
      jacobiExp ((n:ℂ)*p+w)=(rectangularProductNome t)^n*jacobiExp w := by
    rw [hQ]
    unfold jacobiExp
    rw [show I*(Real.pi:ℂ)*((n:ℂ)*p+w)=n*(I*Real.pi*p)+I*Real.pi*w by ring,
      Complex.exp_add,Complex.exp_nat_mul]
  have prod {w : ℂ} (reg : w∉R.lattice) : jacobiFactorProduct (rectangularProductNome t) (jacobiExp w)≠0 := by
    apply jacobiFactorProduct_ne_zero (rectangular_product_nome_norm ht)
    intro n bad
    have e := whole ((sumexp (n+1) w).trans (sub_eq_zero.mp bad).symm)
    have mem : (((n+1:ℕ):ℂ)*p)∈R.lattice := by
      exact PeriodPair.mem_lattice.mpr ⟨0,(n+1:ℕ),by simp [p]⟩
    exact reg (by simpa only [add_sub_cancel_left] using R.lattice.sub_mem e mem)
  have neg : -z∉R.lattice := by simpa using off
  change Complex.exp _*((1-jacobiExp z)*jacobiFactorProduct (rectangularProductNome t) (jacobiExp z)*
    jacobiFactorProduct (rectangularProductNome t) (jacobiExp z)⁻¹)≠0
  rw [← jacobiExp_neg]
  exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr (fun h => off (whole h.symm))) (prod off)) (prod neg))

theorem rectangular_product_log_period_two (t : ℝ) (z : ℂ) :
    logDeriv (jacobiThetaProduct (rectangularProductNome t)) (z+2)=
    logDeriv (jacobiThetaProduct (rectangularProductNome t)) z := by
  let F := jacobiThetaProduct (rectangularProductNome t)
  have e : (fun w : ℂ => F (w+2))=fun w => (-1:ℂ)*F w := by
    funext w
    rw [neg_one_mul]
    exact jacobiThetaProduct_add_two _ _
  calc logDeriv F (z+2)=logDeriv (fun w : ℂ => F (w+2)) z := by rw [logDeriv_apply,logDeriv_apply,deriv_comp_add_const]
       _ = logDeriv F z := by rw [e,logDeriv_const_mul z _ (by norm_num)]

theorem rectangular_product_log_period_imag {t : ℝ} (ht : 0<t) {z : ℂ}
    (off : z∉(manuscriptRectangularLattice t ht).lattice) :
    let R := manuscriptRectangularLattice t ht
    let F := jacobiThetaProduct (rectangularProductNome t)
    logDeriv F (z+R.ω₂)=logDeriv F z-I*(Real.pi:ℂ) := by
  let R := manuscriptRectangularLattice t ht
  let p := R.ω₂
  let Q := rectangularProductNome t
  let F := jacobiThetaProduct Q
  let a := -Complex.exp (-I*(Real.pi:ℂ)*p/2)
  let U := fun w : ℂ => Complex.exp ((-I*(Real.pi:ℂ))*w)
  have hp : Q=jacobiExp p := by simp [Q,p,R,manuscriptRectangularLattice,rectangularPeriodPair,slantedPeriodPair,rectangularProductNome]
  have e : (fun w : ℂ => F (w+p))=fun w => a*(U w*F w) := by
    funext w
    rw [← mul_assoc]
    exact jacobiThetaProduct_quasiperiod (rectangular_product_nome_norm ht) hp w
  have u := ((hasDerivAt_id' z).const_mul (-I*(Real.pi:ℂ))).cexp
  have du : HasDerivAt U (U z*(-I*(Real.pi:ℂ))) z := by simpa only [U,mul_one] using u
  have dF := jacobiThetaProduct_differentiable (rectangular_product_nome_norm ht) z
  have uz : U z≠0 := Complex.exp_ne_zero _
  have dU : logDeriv U z= -I*(Real.pi:ℂ) := by rw [logDeriv_apply,du.deriv];field_simp [uz]
  calc logDeriv F (z+p)=logDeriv (fun w : ℂ => F (w+p)) z := by rw [logDeriv_apply,logDeriv_apply,deriv_comp_add_const]
       _ = logDeriv F z-I*Real.pi := by
         rw [e,logDeriv_const_mul z _ (neg_ne_zero.mpr (Complex.exp_ne_zero _))]
         change logDeriv (U*F) z=_
         rw [logDeriv_mul z uz (rectangular_product_regular ht off) du.differentiableAt dF,dU]
         ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rectangular_product_regular
#print axioms TwoAxisHelicoid.rectangular_product_log_period_imag

