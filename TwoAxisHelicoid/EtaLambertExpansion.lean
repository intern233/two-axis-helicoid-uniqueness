import TwoAxisHelicoid.JacobiProductJet
import TwoAxisHelicoid.LambertDivisorSeries
import TwoAxisHelicoid.ZetaHalfPeriod

namespace TwoAxisHelicoid
open Complex ArithmeticFunction
set_option maxHeartbeats 800000
attribute [local irreducible] thetaScaledJet jacobiThetaProduct jacobiSecondSum

theorem thetaEtaExpression_jacobi_second_sum {t : ℝ} (ht : 0 < t) :
    thetaEtaExpression t = (Real.pi : ℂ)^2/12-
      2*(Real.pi : ℂ)^2*jacobiSecondSum (jacobiNome t) 1 := by
  let C := deriv (rhombicProductTheta t) 0/thetaScaledJet t 1 0
  have hC : C ≠ 0 := jacobiTheta_normalization_ne_zero ht
  have he : rhombicProductTheta t = fun z => C*thetaScaledJet t 0 z :=
    funext (rhombicProductTheta_eq_scaled_theta ht)
  have hj := jacobiThetaProduct_third_zero (jacobiNome_norm_lt_one ht) (jacobiNome_ne_zero t)
  change iteratedDeriv 3 (rhombicProductTheta t) 0 =
    (-(Real.pi : ℂ)^2/4+6*(Real.pi : ℂ)^2*jacobiSecondSum (jacobiNome t) 1)*
      deriv (rhombicProductTheta t) 0 at hj
  rw [he,iteratedDeriv_const_mul_field,thetaScaledJet_iteratedDeriv ht,
    deriv_const_mul_field,(thetaScaledJet_hasDerivAt ht 0 0).deriv] at hj
  norm_num only [Nat.zero_add] at hj
  have hs : thetaScaledJet t 3 0 =
      (-(Real.pi : ℂ)^2/4+6*(Real.pi : ℂ)^2*jacobiSecondSum (jacobiNome t) 1)*
        thetaScaledJet t 1 0 := by
    apply mul_left_cancel₀ hC
    linear_combination hj
  unfold thetaEtaExpression
  rw [hs]
  field_simp [thetaScaledJet_one_ne_zero_of_pos ht]
  ring

theorem jacobiSecondSum_ofReal_one (Q : ℝ) :
    jacobiSecondSum (Q : ℂ) 1 =
      ((∑' n : ℕ, jacobiFraction (Q^(n+1))) : ℝ) := by
  simp only [jacobiSecondSum,jacobiFraction,Complex.ofReal_tsum,
    Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_sub,Complex.ofReal_one,mul_one]

theorem lambert_linear_eq_jacobi_fraction {Q : ℝ} (hQ : |Q| < 1) :
    (∑' n : ℕ, (n+1 : ℝ)*Q^(n+1)/(1-Q^(n+1))) =
      ∑' n : ℕ, jacobiFraction (Q^(n+1)) := by
  have hn : ‖Q‖ < 1 := by simpa only [Real.norm_eq_abs] using hQ
  have he := tsum_pow_div_one_sub_eq_tsum_sigma hn 1
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℝ)^1*Q^n/(1-Q^n)),
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (sigma 1 n : ℝ)*Q^n)] at he
  rw [jacobiFraction_series_eq_sigma hn]
  simpa only [pow_one,Nat.cast_add,Nat.cast_one] using he

/-- The manuscript's literal Lambert expansion of the actual half-period
quasiperiod, valid for every positive rhombic height. -/
theorem actual_eta_lambert_expansion {t : ℝ} (ht : 0 < t) :
    thetaZeta t 1 = ((Real.pi^2/12*(1-24*
      (∑' n : ℕ, (n+1 : ℝ)*(-Real.exp (-Real.pi*t))^(n+1)/
        (1-(-Real.exp (-Real.pi*t))^(n+1))))) : ℝ) := by
  let Q := -Real.exp (-Real.pi*t)
  have hQ : |Q| < 1 := by
    simpa only [Q,jacobiNome_eq_neg_exp,norm_neg,Complex.norm_real,
      Real.norm_eq_abs,abs_neg] using jacobiNome_norm_lt_one ht
  rw [thetaZeta_one,thetaEtaExpression_jacobi_second_sum ht,jacobiNome_eq_neg_exp,
    ← Complex.ofReal_neg]
  change (Real.pi : ℂ)^2/12-2*(Real.pi : ℂ)^2*jacobiSecondSum (Q : ℂ) 1 =
    ((Real.pi^2/12*(1-24*(∑' n : ℕ, (n+1 : ℝ)*Q^(n+1)/(1-Q^(n+1))))) : ℝ)
  rw [jacobiSecondSum_ofReal_one,lambert_linear_eq_jacobi_fraction hQ]
  push_cast
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_eta_lambert_expansion
