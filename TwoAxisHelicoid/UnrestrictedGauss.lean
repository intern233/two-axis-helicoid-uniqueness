import TwoAxisHelicoid.GaussDifferential
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaSigma thetaZeta thetaEtaExpression
set_option maxHeartbeats 1200000

/-- The integrated Gauss differential before the single-valuedness
conditions have quantized its parameters. -/
noncomputable def unrestrictedGauss (t a : ℝ) (κ β z : ℂ) : ℂ :=
  Complex.exp (-κ*thetaZeta t z+β*z)*thetaSigma t (z-a)/thetaSigma t (z+a)

theorem unrestrictedGauss_ne_zero {t : ℝ} (ht : 0 < t) (a : ℝ) (κ β : ℂ) {z : ℂ}
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) : unrestrictedGauss t a κ β z ≠ 0 := by
  unfold unrestrictedGauss
  exact div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _)
    (mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z-a)).mp hm))
      (mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp)

theorem unrestrictedGauss_hasDerivAt {t : ℝ} (ht : 0 < t) (a : ℝ) (κ β : ℂ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    HasDerivAt (unrestrictedGauss t a κ β)
      (unrestrictedGauss t a κ β z*(κ*(rhombicPeriodPair t ht).weierstrassP z+β+
        thetaZeta t (z-a)-thetaZeta t (z+a))) z := by
  have hsm := (thetaSigma_hasDerivAt_zeta_of_pos ht ht hm).comp (h := fun w : ℂ => w-a) z
    ((hasDerivAt_id z).sub_const (a:ℂ))
  have hsp := (thetaSigma_hasDerivAt_zeta_of_pos ht ht hp).comp (h := fun w : ℂ => w+a) z
    ((hasDerivAt_id z).add_const (a:ℂ))
  have he := (((thetaZeta_hasDerivAt_of_pos ht ht hz).const_mul (-κ)).add
    ((hasDerivAt_id z).const_mul β)).cexp
  have hd := (he.mul hsm).div hsp
    (mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp)
  convert hd using 1
  · rfl
  · simp only [Function.comp_apply,Pi.mul_apply,Pi.add_apply,id_eq,mul_one]
    unfold unrestrictedGauss
    have hn := mt (thetaSigma_zero_iff_lattice_of_pos ht ht (z+a)).mp hp
    field_simp

theorem unrestrictedGauss_log_derivative {t : ℝ} (ht : 0 < t) (a : ℝ) (κ β : ℂ) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    deriv (unrestrictedGauss t a κ β) z/unrestrictedGauss t a κ β z =
      κ*(rhombicPeriodPair t ht).weierstrassP z+β+thetaZeta t (z-a)-thetaZeta t (z+a) := by
  rw [(unrestrictedGauss_hasDerivAt ht a κ β hz hm hp).deriv]
  exact mul_div_cancel_left₀ _ (unrestrictedGauss_ne_zero ht a κ β hm hp)

theorem unrestrictedGauss_quasiperiod {t a : ℝ} (κ β : ℂ) {z w k : ℂ}
    (hs : ∀ v, thetaSigma t (v+w) = -Complex.exp (k*(v+w/2))*thetaSigma t v)
    (hz : thetaZeta t (z+w) = thetaZeta t z+k) :
    unrestrictedGauss t a κ β (z+w) =
      Complex.exp (β*w-(κ+2*a)*k)*unrestrictedGauss t a κ β z := by
  have hm : z+w-a = (z-a)+w := by ring
  have hp : z+w+a = (z+a)+w := by ring
  have he : Complex.exp (-κ*(thetaZeta t z+k)+β*(z+w))*Complex.exp (k*(z-a+w/2)) =
      Complex.exp (k*(z+a+w/2))*(Complex.exp (β*w-(κ+2*a)*k)*
        Complex.exp (-κ*thetaZeta t z+β*z)) := by
    simp only [← Complex.exp_add]
    congr 1
    ring
  unfold unrestrictedGauss
  rw [hm,hp,hs,hs,hz]
  calc
    _ = (Complex.exp (-κ*(thetaZeta t z+k)+β*(z+w))*Complex.exp (k*(z-a+w/2)))*
        thetaSigma t (z-a)/(Complex.exp (k*(z+a+w/2))*thetaSigma t (z+a)) := by ring
    _ = Complex.exp (k*(z+a+w/2))*(Complex.exp (β*w-(κ+2*a)*k)*
        Complex.exp (-κ*thetaZeta t z+β*z)*thetaSigma t (z-a))/
        (Complex.exp (k*(z+a+w/2))*thetaSigma t (z+a)) := by rw [he]; congr 1; ring
    _ = Complex.exp (β*w-(κ+2*a)*k)*Complex.exp (-κ*thetaZeta t z+β*z)*
        thetaSigma t (z-a)/thetaSigma t (z+a) :=
      mul_div_mul_left _ _ (Complex.exp_ne_zero _)
    _ = _ := by ring

/-- Real coefficients and trivial multipliers on both primitive periods
force the integer family; the integer is not an input assumption. -/
theorem gauss_real_multiplier_quantization (a κ β η t : ℝ)
    (h₂ : Complex.exp (((2*β-2*(κ+2*a)*η : ℝ) : ℂ)) = 1)
    (hτ : Complex.exp ((β : ℂ)*(1+I*t)-((κ+2*a : ℝ) : ℂ)*
      ((η : ℂ)*(1+I*t)-Real.pi*I)) = 1) :
    ∃ m : ℤ, κ = 2*((m : ℝ)-a) ∧ β = 2*(m : ℝ)*η := by
  have he₂ : Real.exp (2*β-2*(κ+2*a)*η) = 1 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_exp,Complex.ofReal_one] using h₂
  have hβ : β = (κ+2*a)*η := by
    have hzero : 2*β-2*(κ+2*a)*η = 0 := Real.exp_injective (by simpa only [Real.exp_zero] using he₂)
    linarith
  have heτ : (β : ℂ)*(1+I*t)-((κ+2*a : ℝ) : ℂ)*
      ((η : ℂ)*(1+I*t)-Real.pi*I) = ((κ+2*a : ℝ) : ℂ)*Real.pi*I := by
    rw [hβ]
    push_cast
    ring
  rw [heτ] at hτ
  obtain ⟨m,hm⟩ := Complex.exp_eq_one_iff.mp hτ
  have him := congrArg Complex.im hm
  norm_num [Complex.mul_im,Complex.mul_re] at him
  have hκ : κ+2*a = 2*(m : ℝ) := by nlinarith [Real.pi_pos]
  exact ⟨m,by linarith,by rw [hβ,hκ]⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.unrestrictedGauss_log_derivative
#print axioms TwoAxisHelicoid.gauss_real_multiplier_quantization
