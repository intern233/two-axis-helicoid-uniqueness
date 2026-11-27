import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Ring.Int.Parity

namespace TwoAxisHelicoid
open Complex

/-- Odd theta characteristic without its everywhere nonzero exponential factor. -/
noncomputable def jacobiOdd (z tau : ℂ) : ℂ := jacobiTheta₂ (z+(tau+1)/2) tau

theorem jacobiTheta_add_right_one (z tau : ℂ) :
    jacobiTheta₂ z (tau+1) = jacobiTheta₂ (z+1/2) tau := by
  unfold jacobiTheta₂
  apply tsum_congr
  intro n
  obtain ⟨k,hk⟩ := Int.even_mul_pred_self n
  have hkC : (n:ℂ)*((n:ℂ)-1) = 2*k := by exact_mod_cast (show n*(n-1)=2*k by omega)
  have he : (2*Real.pi*I*n*z+Real.pi*I*n^2*(tau+1):ℂ) =
      (2*Real.pi*I*n*(z+1/2)+Real.pi*I*n^2*tau)+(k:ℂ)*(2*Real.pi*I) := by
    linear_combination (Real.pi*I)*hkC
  simp only [jacobiTheta₂_term,he,Complex.exp_add,Complex.exp_int_mul,
    Complex.exp_two_pi_mul_I,one_zpow,mul_one]

theorem jacobiOdd_add_right_one (z tau : ℂ) : jacobiOdd z (tau+1) = jacobiOdd z tau := by
  unfold jacobiOdd
  rw [jacobiTheta_add_right_one]
  have he : z+(tau+1+1)/2+1/2 = (z+(tau+1)/2)+1 := by ring
  rw [he,jacobiTheta₂_add_left]

theorem jacobiTheta_zero_iff_inversion (z : ℂ) {tau : ℂ} (htau : tau ≠ 0) :
    jacobiTheta₂ z tau = 0 ↔ jacobiTheta₂ (z/tau) (-1/tau) = 0 := by
  rw [jacobiTheta₂_functional_equation]
  have hp : (-I*tau)^(1/2:ℂ) ≠ 0 := cpow_ne_zero_iff.mpr
    (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) htau))
  simp only [mul_eq_zero,div_eq_zero_iff,one_ne_zero,hp,or_self,Complex.exp_ne_zero,false_or]

theorem jacobiOdd_zero_iff_inversion (z : ℂ) {tau : ℂ} (htau : tau ≠ 0) :
    jacobiOdd z tau = 0 ↔ jacobiOdd (z/tau) (-1/tau) = 0 := by
  unfold jacobiOdd
  rw [jacobiTheta_zero_iff_inversion _ htau]
  have he : (z+(tau+1)/2)/tau+(-1/tau) = z/tau+((-1/tau)+1)/2 := by
    field_simp
    ring
  have h := jacobiTheta₂_add_left' ((z+(tau+1)/2)/tau) (-1/tau)
  rw [he] at h
  rw [h]
  simp only [mul_eq_zero,Complex.exp_ne_zero,false_or]

theorem jacobiOdd_add_right_two (z tau : ℂ) : jacobiOdd z (tau+2) = jacobiOdd z tau := by
  rw [show tau+2 = (tau+1)+1 by ring,jacobiOdd_add_right_one,jacobiOdd_add_right_one]

theorem jacobiOdd_zero_iff_gamma (z : ℂ) {tau : ℂ} (htau : tau ≠ 0)
    (hden : 2*tau-1 ≠ 0) :
    jacobiOdd z tau = 0 ↔ jacobiOdd (z/(2*tau-1)) ((tau-1)/(2*tau-1)) = 0 := by
  have hu : -1/tau+2 ≠ 0 := by
    intro hu
    apply hden
    field_simp at hu
    linear_combination hu
  have hz : (z/tau)/(-1/tau+2) = z/(2*tau-1) := by field_simp; ring
  have hv : -1/(-1/tau+2)+1 = (tau-1)/(2*tau-1) := by
    rw [show -1/tau+2 = (2*tau-1)/tau by field_simp; ring]
    field_simp
    ring
  calc
    jacobiOdd z tau = 0 ↔ jacobiOdd (z/tau) (-1/tau) = 0 := jacobiOdd_zero_iff_inversion z htau
    _ ↔ jacobiOdd (z/tau) (-1/tau+2) = 0 := by rw [jacobiOdd_add_right_two]
    _ ↔ jacobiOdd ((z/tau)/(-1/tau+2)) (-1/(-1/tau+2)) = 0 :=
      jacobiOdd_zero_iff_inversion _ hu
    _ ↔ jacobiOdd ((z/tau)/(-1/tau+2)) (-1/(-1/tau+2)+1) = 0 := by
      rw [jacobiOdd_add_right_one]
    _ ↔ _ := by rw [hz,hv]

noncomputable def jacobiOddInversionFactor (tau z : ℂ) : ℂ :=
  (1/(-I*tau)^(1/2:ℂ))*Complex.exp
    (-Real.pi*I*(z+(tau+1)/2)^2/tau+Real.pi*I*((-1/tau)+2*((z+(tau+1)/2)/tau)))

theorem jacobiOddInversionFactor_ne_zero {tau : ℂ} (htau : tau ≠ 0) (z : ℂ) :
    jacobiOddInversionFactor tau z ≠ 0 := by
  unfold jacobiOddInversionFactor
  exact mul_ne_zero (div_ne_zero one_ne_zero (cpow_ne_zero_iff.mpr
    (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) htau)))) (Complex.exp_ne_zero _)

theorem jacobiOddInversionFactor_differentiable (tau : ℂ) :
    Differentiable ℂ (jacobiOddInversionFactor tau) := by
  unfold jacobiOddInversionFactor
  fun_prop

theorem jacobiOdd_inversion (z : ℂ) {tau : ℂ} (htau : tau ≠ 0) :
    jacobiOdd z tau = jacobiOddInversionFactor tau z*jacobiOdd (z/tau) (-1/tau) := by
  unfold jacobiOdd
  have he : (z+(tau+1)/2)/tau+(-1/tau) = z/tau+((-1/tau)+1)/2 := by
    field_simp
    ring
  have hq := jacobiTheta₂_add_left' ((z+(tau+1)/2)/tau) (-1/tau)
  rw [he] at hq
  rw [jacobiTheta₂_functional_equation (z+(tau+1)/2) tau,hq]
  unfold jacobiOddInversionFactor
  have hexp : Complex.exp (Real.pi*I*((-1/tau)+2*((z+(tau+1)/2)/tau)))*
      Complex.exp (-Real.pi*I*((-1/tau)+2*((z+(tau+1)/2)/tau))) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    ring
  rw [Complex.exp_add]
  linear_combination -(1/(-I*tau)^(1/2:ℂ)*
    Complex.exp (-Real.pi*I*(z+(tau+1)/2)^2/tau)*
    jacobiTheta₂ ((z+(tau+1)/2)/tau) (-1/tau))*hexp

theorem jacobiOdd_gamma (z : ℂ) {tau : ℂ} (htau : tau ≠ 0) (hden : 2*tau-1 ≠ 0) :
    jacobiOdd z tau = (jacobiOddInversionFactor tau z*
      jacobiOddInversionFactor (-1/tau+2) (z/tau))*
        jacobiOdd (z/(2*tau-1)) ((tau-1)/(2*tau-1)) := by
  have hu : -1/tau+2 ≠ 0 := by
    intro hu
    apply hden
    field_simp at hu
    linear_combination hu
  have hz : (z/tau)/(-1/tau+2) = z/(2*tau-1) := by field_simp; ring
  have hv : -1/(-1/tau+2)+1 = (tau-1)/(2*tau-1) := by
    rw [show -1/tau+2 = (2*tau-1)/tau by field_simp; ring]
    field_simp
    ring
  rw [jacobiOdd_inversion z htau]
  rw [← jacobiOdd_add_right_two (z/tau) (-1/tau),jacobiOdd_inversion (z/tau) hu]
  rw [← jacobiOdd_add_right_one ((z/tau)/(-1/tau+2)) (-1/(-1/tau+2)),hz,hv]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiOdd_zero_iff_inversion
