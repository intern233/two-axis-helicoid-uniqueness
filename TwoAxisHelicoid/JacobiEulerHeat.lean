import TwoAxisHelicoid.JacobiEulerParameter
import TwoAxisHelicoid.EtaLambertExpansion
import TwoAxisHelicoid.EllipticEtaHeat

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 1000000
attribute [local irreducible] jacobiEulerProduct thetaScaledJet

noncomputable def rhombicEulerProduct (t : ℝ) : ℂ := jacobiEulerProduct (jacobiNome t)

theorem jacobiNome_hasDerivAt (t : ℝ) :
    HasDerivAt jacobiNome (-(Real.pi : ℂ)*jacobiNome t) t := by
  have he : jacobiNome = fun s : ℝ => -(Real.exp (-Real.pi*s) : ℂ) :=
    funext jacobiNome_eq_neg_exp
  rw [he]
  have hd := (((hasDerivAt_id t).const_mul (-Real.pi)).exp.ofReal_comp).neg
  convert hd using 1
  · rfl
  · push_cast
    simp only [mul_one,id_eq]
    ring

theorem rhombic_lambert_one_eq_jacobi_second {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, (n+1 : ℂ)*(jacobiNome t)^(n+1)/(1-(jacobiNome t)^(n+1))) =
      jacobiSecondSum (jacobiNome t) 1 := by
  let Q := -Real.exp (-Real.pi*t)
  have hQ : |Q| < 1 := by
    simpa only [Q,jacobiNome_eq_neg_exp,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_neg] using
      jacobiNome_norm_lt_one ht
  have he : jacobiNome t = (Q : ℂ) := by simp only [Q,Complex.ofReal_neg,jacobiNome_eq_neg_exp]
  rw [he,jacobiSecondSum_ofReal_one,← lambert_linear_eq_jacobi_fraction hQ,Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  push_cast
  rfl

theorem rhombicEulerProduct_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt rhombicEulerProduct
      ((Real.pi : ℂ)*jacobiSecondSum (jacobiNome t) 1*rhombicEulerProduct t) t := by
  have hq := jacobiNome_norm_lt_one ht
  have hn := jacobiEulerProduct_ne_zero hq
  have hd := (jacobiEulerProduct_analyticAt hq).differentiableAt.hasDerivAt.scomp t
    (jacobiNome_hasDerivAt t)
  have hl := jacobiEulerProduct_logDeriv_mul hq (jacobiNome_ne_zero t)
  rw [rhombic_lambert_one_eq_jacobi_second ht,logDeriv_apply] at hl
  field_simp [hn] at hl
  convert hd using 1
  · rfl
  · change _ = (-(Real.pi : ℂ)*jacobiNome t)*deriv jacobiEulerProduct (jacobiNome t)
    dsimp [rhombicEulerProduct]
    linear_combination (Real.pi : ℂ)*hl

theorem thetaScaledJet_one_parameter_euler_ode {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => thetaScaledJet s 1 0)
      (3*(Real.pi : ℂ)*jacobiSecondSum (jacobiNome t) 1*thetaScaledJet t 1 0) t := by
  have h3 : thetaScaledJet t 3 0 = -3*thetaEtaExpression t*thetaScaledJet t 1 0 := by
    unfold thetaEtaExpression
    field_simp [thetaScaledJet_one_ne_zero_of_pos ht]
  have hd := thetaScaledJet_parameter_hasDerivAt ht 1 0
  rw [show 1+2 = 3 by rfl,h3,thetaEtaExpression_jacobi_second_sum ht] at hd
  convert hd using 1
  field_simp
  ring

noncomputable def thetaEulerNormalization (t : ℝ) : ℂ :=
  thetaScaledJet t 1 0/(rhombicEulerProduct t)^3

theorem thetaEulerNormalization_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt thetaEulerNormalization 0 t := by
  have hn : rhombicEulerProduct t ≠ 0 := jacobiEulerProduct_ne_zero (jacobiNome_norm_lt_one ht)
  have hd := (thetaScaledJet_one_parameter_euler_ode ht).div
    ((rhombicEulerProduct_hasDerivAt ht).pow 3) (pow_ne_zero _ hn)
  convert hd using 1
  · rfl
  · simp only [Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub]
    ring

theorem thetaEulerNormalization_eq {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    thetaEulerNormalization t = thetaEulerNormalization s := by
  exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun u hu => (thetaEulerNormalization_hasDerivAt hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (thetaEulerNormalization_hasDerivAt hu).deriv) ht hs

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaEulerNormalization_eq
