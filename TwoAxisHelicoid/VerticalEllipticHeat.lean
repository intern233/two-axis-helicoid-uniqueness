import TwoAxisHelicoid.WeightedPeriodContinuity
import TwoAxisHelicoid.VerticalBranchDerivative
import TwoAxisHelicoid.WeierstrassSecondOrder

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaJet thetaQuotient thetaG thetaGa thetaGt
  thetaLogSecond thetaLogThird thetaLogFourth verticalA

theorem thetaLogSecond_parameter_hasDerivAt {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : thetaJet t 0 (Real.pi*z/2) ≠ 0) :
    HasDerivAt (fun s : ℝ => thetaLogSecond s z)
      ((thetaLogFourth t z/2-thetaLogSecond t z^2+
        (thetaZeta t z-thetaEtaExpression t*z)*thetaLogThird t z)/(Real.pi:ℂ)) t := by
  have h1 := thetaQuotient_parameter_hasDerivAt ht 1 (Real.pi*z/2) hz
  have h2 := thetaQuotient_parameter_hasDerivAt ht 2 (Real.pi*z/2) hz
  have hd := ((h1.pow 2).sub h2).const_mul (Real.pi^2/4:ℂ)
  convert hd using 1
  · funext s
    simp only [thetaLogSecond,Pi.sub_apply,Pi.pow_apply]
  · rw [thetaZeta_quotient]
    unfold thetaLogSecond thetaLogThird thetaLogFourth
    norm_num
    field_simp
    ring

theorem thetaG_parameter_heat_identity (t a : ℝ) :
    (Real.pi:ℂ)*thetaGt t a = thetaLogFourth t a/2-thetaLogSecond t a^2+
      (thetaZeta t a-thetaEtaExpression t*a)*thetaGa t a+((Real.pi/t:ℝ):ℂ)^2 := by
  rw [thetaZeta_quotient]
  unfold thetaGt thetaGa thetaLogSecond thetaLogFourth
  push_cast
  rw [div_pow]
  ring

theorem thetaG_parameter_heat_at_root {t a : ℝ} (hG : thetaG t a = 0) :
    (Real.pi:ℂ)*thetaGt t a = thetaLogFourth t a/2+
      (thetaZeta t a-thetaEtaExpression t*a)*thetaGa t a := by
  have he : thetaLogSecond t a = ((Real.pi/t:ℝ):ℂ) := by
    unfold thetaG at hG
    unfold thetaLogSecond
    exact sub_eq_zero.mp hG
  rw [thetaG_parameter_heat_identity,he]
  ring

theorem verticalA_deriv_elliptic_formula {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    deriv verticalA t = -((thetaZeta t (verticalA t)).re-
      (thetaEtaExpression t).re*verticalA t+
      (deriv (rhombicPeriodPair t ht.1).derivWeierstrassP (verticalA t)).re/
        (2*((rhombicPeriodPair t ht.1).derivWeierstrassP (verticalA t)).re))/Real.pi := by
  have ha := (verticalA_spec ht).1
  have hz := real_not_mem_rhombic_lattice_of_pos ht.1 ha.1 (by linarith [ha.2])
  have hv := (thetaGa_re_neg_unit ht.1 ha.1 ha.2).ne
  have hheat := congrArg Complex.re (thetaG_parameter_heat_at_root (verticalA_spec ht).2)
  simp only [Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,thetaEtaExpression_real,thetaZeta_real,
    zero_mul,mul_zero,sub_zero,zero_sub,Complex.add_re,Complex.div_ofNat_re] at hheat
  rw [(verticalA_hasDerivAt ht).deriv]
  rw [← thetaLogFourth_eq_weierstrassP_second ht.1 hz,
    ← thetaGa_re_eq_wp_deriv ht.1 ha.1 (by linarith [ha.2])]
  field_simp [Real.pi_ne_zero,hv]
  nlinarith [hheat]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaLogSecond_parameter_hasDerivAt
#print axioms TwoAxisHelicoid.verticalA_deriv_elliptic_formula
