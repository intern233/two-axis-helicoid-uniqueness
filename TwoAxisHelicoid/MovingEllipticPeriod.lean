import TwoAxisHelicoid.ComplexPeriodEllipticHeat
import TwoAxisHelicoid.VerticalEllipticHeat

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaW thetaP actualPeriodAlong verticalA

theorem thetaW_real (t a : ℝ) : (thetaW t a).im = 0 := by
  simp only [thetaW,Complex.sub_im,Complex.mul_im,Complex.ofReal_im,
    thetaZeta_real,thetaEtaExpression_real,zero_mul,mul_zero,add_zero,sub_zero]

theorem fullComplexPeriod_da_re {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    (deriv (fullComplexPeriod t) a).re = horizontalPeriodDa t a := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a
    (fullComplexPeriod_a_hasDerivAt ht ha).differentiableAt.hasDerivAt
  have hd' : HasDerivAt (thetaHorizontalPeriod t) (deriv (fullComplexPeriod t) a).re a := by
    convert hd using 1
    · funext b
      exact (fullComplexPeriod_re t b).symm
    · rfl
  exact hd'.unique (horizontal_period_a_hasDerivAt ht ha)

theorem horizontalPeriodDt_elliptic_intermediate {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    Real.pi*horizontalPeriodDt t a = 3*(fullComplexWeight t ht a).re+
      (2*((rhombicPeriodPair t ht).weierstrassP a).re-(thetaEtaExpression t).re)*thetaHorizontalPeriod t a+
      (thetaW t a).re*horizontalPeriodDa t a-(a-1)*(fullComplexSlopeWeight t ht a).re := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (fullComplexPeriod_t_elliptic_intermediate ht ha)
  have hd' : HasDerivAt (fun s => thetaHorizontalPeriod s a)
      (((3*fullComplexWeight t ht a+
        (2*(rhombicPeriodPair t ht).weierstrassP a-thetaEtaExpression t)*fullComplexPeriod t a+
        thetaW t a*deriv (fullComplexPeriod t) a-(a-1)*fullComplexSlopeWeight t ht a)/(Real.pi:ℂ)).re) t := by
    convert hd using 1
    · funext s
      exact (fullComplexPeriod_re s a).symm
    · rfl
  have he := (horizontal_period_t_hasDerivAt ht ha).unique hd'
  simp only [Complex.div_ofReal_re,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.sub_im,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
    Complex.one_re,Complex.one_im,thetaW_real,thetaEtaExpression_real,rhombic_weierstrassP_real,
    zero_mul,mul_zero,add_zero,sub_zero,fullComplexPeriod_re,fullComplexPeriod_da_re ht ha] at he
  exact (mul_comm _ _).trans ((eq_div_iff Real.pi_ne_zero).mp he)

noncomputable def periodD (t a : ℝ) : ℝ := (thetaLogFourth t a).re/(2*(thetaGa t a).re)

theorem verticalA_deriv_WD {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    deriv verticalA t = -((thetaW t (verticalA t)).re+periodD t (verticalA t))/Real.pi := by
  have ha := (verticalA_spec ht).1
  have hz := real_not_mem_rhombic_lattice_of_pos ht.1 ha.1 (by linarith [ha.2])
  rw [verticalA_deriv_elliptic_formula ht]
  unfold periodD thetaW
  rw [thetaLogFourth_eq_weierstrassP_second ht.1 hz,thetaGa_re_eq_wp_deriv ht.1 ha.1 (by linarith [ha.2])]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem actualPeriodAlong_moving_elliptic_identity {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    Real.pi*deriv actualPeriodAlong t =
      (2*((rhombicPeriodPair t ht.1).weierstrassP (verticalA t)).re-(thetaEtaExpression t).re+
        2*periodD t (verticalA t)*(thetaW t (verticalA t)).re+
        2*periodD t (verticalA t)*(verticalA t-1)*(thetaEtaExpression t).re)*actualPeriodAlong t+
      (3+2*periodD t (verticalA t)*(verticalA t-1))*(fullComplexWeight t ht.1 (verticalA t)).re-
      (verticalA t-1)*(fullComplexSlopeWeight t ht.1 (verticalA t)).re := by
  have ha : verticalA t ∈ Ioo (0:ℝ) 2 := ⟨(verticalA_spec ht).1.1,by linarith [(verticalA_spec ht).1.2]⟩
  have hdt := horizontalPeriodDt_elliptic_intermediate ht.1 ha
  have hda := horizontalPeriodDa_elliptic_formula ht.1 ha
  rw [thetaWeightedPeriod_eq_fullComplexWeight ht.1] at hda
  have hk : periodK t (verticalA t) = -2*((thetaW t (verticalA t)).re+
      (verticalA t-1)*(thetaEtaExpression t).re) := by
    unfold periodK thetaW
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    ring
  rw [hk] at hda
  rw [(actualPeriodAlong_hasDerivAt ht).deriv,verticalA_deriv_WD ht]
  change Real.pi*(horizontalPeriodDt t (verticalA t)+
      (-((thetaW t (verticalA t)).re+periodD t (verticalA t))/Real.pi)*horizontalPeriodDa t (verticalA t)) = _
  unfold actualPeriodAlong
  field_simp [Real.pi_ne_zero]
  linear_combination hdt-periodD t (verticalA t)*hda

theorem actualPeriodAlong_zero_derivative_elliptic {t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) (hzero : actualPeriodAlong t = 0) :
    Real.pi*deriv actualPeriodAlong t =
      (3+2*periodD t (verticalA t)*(verticalA t-1))*(fullComplexWeight t ht.1 (verticalA t)).re-
      (verticalA t-1)*(fullComplexSlopeWeight t ht.1 (verticalA t)).re := by
  rw [actualPeriodAlong_moving_elliptic_identity ht,hzero,mul_zero,zero_add]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_moving_elliptic_identity
#print axioms TwoAxisHelicoid.actualPeriodAlong_zero_derivative_elliptic
