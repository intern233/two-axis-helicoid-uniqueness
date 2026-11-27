import TwoAxisHelicoid.JacobiProductCore
import TwoAxisHelicoid.ThetaQuasiPeriod
import TwoAxisHelicoid.RhombicLattice

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 400000
attribute [local irreducible] jacobiFactorProduct jacobiThetaProductCore jacobiThetaProduct

noncomputable def jacobiNome (t : ℝ) : ℂ :=
  Complex.exp (I*(Real.pi : ℂ)*(1+I*t))

theorem jacobiNome_norm (t : ℝ) : ‖jacobiNome t‖ = Real.exp (-Real.pi*t) := by
  rw [jacobiNome, Complex.norm_exp]
  congr 1
  norm_num [Complex.mul_re, Complex.mul_im]

theorem jacobiNome_norm_lt_one {t : ℝ} (ht : 0 < t) : ‖jacobiNome t‖ < 1 := by
  rw [jacobiNome_norm, Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) ht

theorem jacobiNome_ne_zero (t : ℝ) : jacobiNome t ≠ 0 := Complex.exp_ne_zero _

theorem jacobiNome_eq_neg_exp (t : ℝ) :
    jacobiNome t = -(Real.exp (-Real.pi*t) : ℂ) := by
  have he : (I*(Real.pi : ℂ)*(1+I*t)) = (Real.pi : ℂ)*I+(-Real.pi*t : ℝ) := by
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  rw [jacobiNome, he, Complex.exp_add, Complex.exp_pi_mul_I, Complex.ofReal_exp]
  ring

noncomputable def rhombicProductTheta (t : ℝ) : ℂ → ℂ :=
  jacobiThetaProduct (jacobiNome t)

theorem jacobiThetaProduct_add_two (q z : ℂ) :
    jacobiThetaProduct q (z+2) = -jacobiThetaProduct q z := by
  have hx : Complex.exp (I*(Real.pi : ℂ)*(z+2)) = Complex.exp (I*(Real.pi : ℂ)*z) := by
    rw [show I*(Real.pi : ℂ)*(z+2) = I*Real.pi*z+2*Real.pi*I by ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have he : Complex.exp (-I*(Real.pi : ℂ)*(z+2)/2) =
      -Complex.exp (-I*(Real.pi : ℂ)*z/2) := by
    rw [show -I*(Real.pi : ℂ)*(z+2)/2 = -I*Real.pi*z/2+-(Real.pi*I) by ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  simp only [jacobiThetaProduct, hx, he]
  ring

theorem jacobiThetaProduct_quasiperiod {q : ℂ} (hq : ‖q‖ < 1) {p : ℂ}
    (hp : q = Complex.exp (I*(Real.pi : ℂ)*p)) (z : ℂ) :
    jacobiThetaProduct q (z+p) =
      (-Complex.exp (-I*(Real.pi : ℂ)*p/2)*Complex.exp (-I*(Real.pi : ℂ)*z))*
        jacobiThetaProduct q z := by
  have hq0 : q ≠ 0 := by rw [hp]; exact Complex.exp_ne_zero _
  have hx : Complex.exp (I*(Real.pi : ℂ)*(z+p)) =
      q*Complex.exp (I*(Real.pi : ℂ)*z) := by
    rw [mul_add, Complex.exp_add, hp]
    ring
  have he : Complex.exp (-I*(Real.pi : ℂ)*(z+p)/2) =
      Complex.exp (-I*(Real.pi : ℂ)*p/2)*Complex.exp (-I*(Real.pi : ℂ)*z/2) := by
    rw [show -I*(Real.pi : ℂ)*(z+p)/2 = -I*Real.pi*p/2+(-I*Real.pi*z/2) by ring,
      Complex.exp_add]
  simp only [jacobiThetaProduct, hx, he,
    jacobiThetaProductCore_shift hq hq0 (Complex.exp_ne_zero _), ← Complex.exp_neg]
  rw [show -(I*(Real.pi : ℂ)*z) = -I*Real.pi*z by ring]
  ring

theorem rhombicProductTheta_quasiperiod {t : ℝ} (ht : 0 < t) (z : ℂ) :
    rhombicProductTheta t (z+(1+I*t)) =
      thetaQuasiFactor t (Real.pi*z/2)*rhombicProductTheta t z := by
  rw [rhombicProductTheta,
    jacobiThetaProduct_quasiperiod (jacobiNome_norm_lt_one ht) rfl]
  congr 1
  have he : (Real.pi : ℂ)*I+(-I*Real.pi*(1+I*t)/2)+(-I*Real.pi*z) =
      Real.pi*I/2+Real.pi*t/2-2*(Real.pi*z/2)*I := by
    ring_nf
    simp only [I_sq]
    ring
  calc
    _ = (Complex.exp ((Real.pi : ℂ)*I)*
        Complex.exp (-I*(Real.pi : ℂ)*(1+I*t)/2))*Complex.exp (-I*(Real.pi : ℂ)*z) := by
      rw [Complex.exp_pi_mul_I]
      ring
    _ = Complex.exp ((Real.pi : ℂ)*I+(-I*Real.pi*(1+I*t)/2)+(-I*Real.pi*z)) := by
      rw [Complex.exp_add, Complex.exp_add]
    _ = _ := by rw [he]; rfl

theorem rhombicProductTheta_differentiable {t : ℝ} (ht : 0 < t) :
    Differentiable ℂ (rhombicProductTheta t) :=
  jacobiThetaProduct_differentiable (jacobiNome_norm_lt_one ht)

theorem rhombicProductTheta_zero (t : ℝ) : rhombicProductTheta t 0 = 0 :=
  jacobiThetaProduct_zero _

theorem rhombicProductTheta_zero_at_lattice {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ (rhombicPeriodPair t ht).lattice) : rhombicProductTheta t z = 0 := by
  have htwo : Function.Periodic (fun w => rhombicProductTheta t w = 0) 2 := by
    intro w
    simp only [rhombicProductTheta, jacobiThetaProduct_add_two, neg_eq_zero]
  have hhalf : Function.Periodic (fun w => rhombicProductTheta t w = 0) (1+I*t) := by
    intro w
    change (rhombicProductTheta t (w+(1+I*t)) = 0) = (rhombicProductTheta t w = 0)
    apply propext
    rw [rhombicProductTheta_quasiperiod ht, mul_eq_zero]
    simp only [thetaQuasiFactor, Complex.exp_ne_zero, false_or]
  obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hz
  change (m : ℂ)*2+(n : ℂ)*(1+I*t) = z at he
  rw [← he]
  have h1 := hhalf.zsmul n ((m : ℂ)*2)
  have h2 := htwo.zsmul_eq m
  simp only [zsmul_eq_mul] at h1 h2
  rw [h1, h2]
  exact rhombicProductTheta_zero t

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rhombicProductTheta_quasiperiod
#print axioms TwoAxisHelicoid.rhombicProductTheta_zero_at_lattice
