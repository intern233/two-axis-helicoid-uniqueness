import TwoAxisHelicoid.EllipticFHeat
import TwoAxisHelicoid.VerticalBranchLimit
import TwoAxisHelicoid.SecondOrderMean
import TwoAxisHelicoid.ThetaParity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaQuotient thetaG thetaGa thetaLogThird thetaLogFourth

theorem thetaJet_three_half_pi (t : ℝ) : thetaJet t 3 (Real.pi/2) = 0 := by
  have h := thetaJet_add_pi t 3 (-(Real.pi/2:ℂ))
  rw [show -(Real.pi/2:ℂ)+Real.pi=Real.pi/2 by ring,thetaJet_neg] at h
  norm_num only [pow_succ,neg_one_mul,one_mul,neg_neg] at h
  linear_combination (1/2:ℂ)*h

theorem thetaGa_one (t : ℝ) : thetaGa t 1 = 0 := by
  simp [thetaGa,thetaQuotient,thetaJet_one_half_pi,thetaJet_three_half_pi]

theorem thetaGa_real_hasDerivAt {t a : ℝ} (ht : 0 < t) (ha0 : 0 < a) (ha2 : a < 2) :
    HasDerivAt (fun b : ℝ => (thetaGa t b).re) (thetaLogFourth t a).re a := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a
    (thetaLogThird_hasDerivAt ht (theta_vertical_denominator ht ha0 ha2)).comp_ofReal
  convert hd using 1
  · funext b
    simp only [thetaGa,thetaLogThird,Function.comp_apply,Complex.reCLM_apply]
  · rfl

theorem thetaLogFourth_real_joint_continuousAt {t a : ℝ} (ht : 0 < t)
    (ha0 : 0 < a) (ha2 : a < 2) :
    ContinuousAt (fun p : ℝ × ℝ => (thetaLogFourth p.1 p.2).re) (t,a) := by
  have h1 := theta_vertical_quotient_continuousAt ht ha0 ha2 1
  have h2 := theta_vertical_quotient_continuousAt ht ha0 ha2 2
  have h3 := theta_vertical_quotient_continuousAt ht ha0 ha2 3
  have h4 := theta_vertical_quotient_continuousAt ht ha0 ha2 4
  unfold thetaLogFourth
  apply Complex.continuous_re.continuousAt.comp
  exact continuousAt_const.mul
    (((((continuousAt_const.mul (h2.pow 2)).sub ((continuousAt_const.mul (h1.pow 2)).mul h2)).add
      (continuousAt_const.mul (h1.pow 4))).add ((continuousAt_const.mul h1).mul h3)).sub h4)

theorem thetaLogFourth_one_re {t : ℝ} (ht : 0 < t) :
    (thetaLogFourth t 1).re = ellipticC t ht := by
  have hz : (1:ℂ) ∉ (rhombicPeriodPair t ht).lattice :=
    real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  rw [thetaLogFourth_eq_weierstrassP_second ht hz]
  rfl

theorem vertical_root_second_order_mean {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    ∃ c ∈ Ioo (verticalA t) 1,
      -(thetaG t 1).re = (thetaLogFourth t c).re / 2 * (1-verticalA t)^2 := by
  have ha := verticalA_spec ht
  obtain ⟨c,hc,he⟩ := exists_second_order_mean ha.1.2
    (fun x hx => thetaG_real_a_hasDerivAt ht.1 (ha.1.1.trans_le hx.1) (by linarith [hx.2]))
    (fun x hx => thetaGa_real_hasDerivAt ht.1 (ha.1.1.trans_le hx.1) (by linarith [hx.2]))
    (by rw [thetaGa_one]; rfl)
  refine ⟨c,hc,?_⟩
  rw [ha.2,Complex.zero_re,zero_sub] at he
  linear_combination he

theorem thetaG_one_t_hasDerivAt_upper :
    HasDerivAt (fun t : ℝ => (thetaG t 1).re)
      (ellipticC ellipticVerticalUpper ellipticVerticalUpper_pos/(2*Real.pi)) ellipticVerticalUpper := by
  let T := ellipticVerticalUpper
  have ht : 0 < T := ellipticVerticalUpper_pos
  have hd := (ellipticFReal_differentiableAt ht).hasDerivAt.sub
    ((hasDerivAt_const T Real.pi).div (hasDerivAt_id T) ht.ne')
  have hf : ellipticFReal T = Real.pi/T := by
    have he := thetaG_one_eq_ellipticFReal T
    rw [thetaG_vertical_upper_one_zero,Complex.zero_re] at he
    linarith
  have hh := ellipticFReal_heat_identity ht
  rw [hf] at hh
  convert hd using 1
  · funext t
    exact thetaG_one_eq_ellipticFReal t
  · change ellipticC T ht/(2*Real.pi) = deriv ellipticFReal T-(0*T-Real.pi*1)/T^2
    field_simp [ht.ne',Real.pi_ne_zero]
    field_simp [ht.ne',Real.pi_ne_zero] at hh
    nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.vertical_root_second_order_mean
#print axioms TwoAxisHelicoid.thetaG_one_t_hasDerivAt_upper
