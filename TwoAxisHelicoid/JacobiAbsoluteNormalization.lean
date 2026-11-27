import TwoAxisHelicoid.JacobiEulerHeat
import TwoAxisHelicoid.ThetaHighHeightLimit

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
attribute [local irreducible] thetaScaledJet jacobiEulerProduct

theorem rhombicEulerProduct_high_height :
    Tendsto rhombicEulerProduct atTop (𝓝 (1 : ℂ)) := by
  have hc := (jacobiEulerProduct_analyticAt (by norm_num : ‖(0 : ℂ)‖ < 1)).continuousAt
  simpa only [jacobiEulerProduct_zero,Function.comp_def,rhombicEulerProduct] using!
    hc.tendsto.comp jacobiNome_high_height

theorem thetaEulerNormalization_value {t : ℝ} (ht : 0 < t) :
    thetaEulerNormalization t = (Real.pi/2 : ℂ) := by
  have hh : Tendsto thetaEulerNormalization atTop (𝓝 (Real.pi/2 : ℂ)) := by
    simpa only [one_pow,div_one,Complex.ofReal_div,Complex.ofReal_ofNat,thetaEulerNormalization] using!
      thetaScaledJet_one_high_height.div (rhombicEulerProduct_high_height.pow 3) (by norm_num)
  have hc : Tendsto (fun _ : ℝ => thetaEulerNormalization t) atTop (𝓝 (Real.pi/2 : ℂ)) := by
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact thetaEulerNormalization_eq hs ht
  exact tendsto_nhds_unique tendsto_const_nhds hc

/-- The absolute derivative normalization of the manuscript's normalized
theta series, obtained by the heat equation and the limit at high height. -/
theorem thetaScaledJet_one_absolute_product {t : ℝ} (ht : 0 < t) :
    thetaScaledJet t 1 0 = (Real.pi/2 : ℂ)*(rhombicEulerProduct t)^3 := by
  have hn : rhombicEulerProduct t ≠ 0 := jacobiEulerProduct_ne_zero (jacobiNome_norm_lt_one ht)
  exact (div_eq_iff (pow_ne_zero _ hn)).mp (thetaEulerNormalization_value ht)

theorem jacobiSineFactor_eq_sin (z : ℂ) :
    jacobiSineFactor z = (-2*I)*sin ((Real.pi/2 : ℂ)*z) := by
  unfold jacobiSineFactor Complex.sin
  have he : -I*(Real.pi : ℂ)/2*z = -((Real.pi/2 : ℂ)*z)*I := by ring
  have he' : I*(Real.pi : ℂ)/2*z = ((Real.pi/2 : ℂ)*z)*I := by ring
  rw [he,he']
  field_simp
  ring_nf
  norm_num [I_sq,sub_eq_add_neg]

/-- The exact Jacobi product, including the absolute normalization that
previously cancelled in the logarithmic derivatives and period kernels. -/
theorem thetaScaledJet_zero_absolute_product {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaScaledJet t 0 z = sin ((Real.pi/2 : ℂ)*z)*rhombicEulerProduct t*
      jacobiFactorProduct (jacobiNome t) (jacobiExp z)*
      jacobiFactorProduct (jacobiNome t) (jacobiExp z)⁻¹ := by
  have hn : rhombicEulerProduct t ≠ 0 := jacobiEulerProduct_ne_zero (jacobiNome_norm_lt_one ht)
  have hd : deriv (rhombicProductTheta t) 0 =
      -I*(Real.pi : ℂ)*(rhombicEulerProduct t)^2 := by
    change deriv (jacobiThetaProduct (jacobiNome t)) 0 = _
    rw [(jacobiThetaProduct_hasDerivAt_zero (jacobiNome_norm_lt_one ht)).deriv,
      ← jacobiEulerProduct_eq_factor]
    rfl
  have h := rhombicProductTheta_eq_scaled_theta ht z
  rw [hd,thetaScaledJet_one_absolute_product ht] at h
  change jacobiThetaProduct (jacobiNome t) z = _ at h
  rw [jacobiThetaProduct_eq_sine_mul,Pi.mul_apply,jacobiSineFactor_eq_sin] at h
  have hC : (-I*(Real.pi : ℂ)*(rhombicEulerProduct t)^2)/
      ((Real.pi/2 : ℂ)*(rhombicEulerProduct t)^3) = (-2*I)/rhombicEulerProduct t := by
    field_simp [hn,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [hC] at h
  field_simp [hn] at h
  unfold jacobiSymmetricProduct at h
  rw [show (Real.pi/2 : ℂ)*z = (Real.pi : ℂ)*z/2 by ring]
  linear_combination h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaScaledJet_one_absolute_product
#print axioms TwoAxisHelicoid.thetaScaledJet_zero_absolute_product
