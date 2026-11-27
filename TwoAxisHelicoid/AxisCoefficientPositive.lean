import TwoAxisHelicoid.WeierstrassVerticalDomain
import TwoAxisHelicoid.EllipticFReciprocal

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval ComplexConjugate
attribute [local irreducible] thetaZeta thetaEtaExpression

theorem rhombic_weierstrassP_real_ge_one {t x : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo (0 : ℝ) 2) :
    ((rhombicPeriodPair t ht).weierstrassP 1).re ≤
      ((rhombicPeriodPair t ht).weierstrassP x).re := by
  have hm := rhombic_weierstrassP_strictAnti_to_one ht
  by_cases h : x ≤ 1
  · simpa only [Complex.ofReal_one] using
      hm.antitoneOn ⟨hx.1,h⟩ (by norm_num : (1 : ℝ) ∈ Ioc 0 1) h
  · have hx' : 2-x ∈ Ioc (0 : ℝ) 1 := by constructor <;> linarith [hx.2]
    have hb := hm.antitoneOn hx' (by norm_num : (1 : ℝ) ∈ Ioc 0 1) hx'.2
    have hp := (rhombicPeriodPair t ht).weierstrassP_add_coe (-(x : ℂ))
      ⟨2,(rhombicPeriodPair t ht).ω₁_mem_lattice⟩
    have he : ((2-x : ℝ) : ℂ) = -(x : ℂ)+2 := by push_cast; ring
    rw [he,hp,(rhombicPeriodPair t ht).weierstrassP_neg] at hb
    simpa only [Complex.ofReal_one] using hb

theorem rhombic_weierstrassP_imaginary_real {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ((rhombicPeriodPair t ht).weierstrassP (I*y)).im = 0 := by
  have h := rhombic_weierstrassP_conj ht (I*y)
  have he : conj (I*(y : ℂ)) = -(I*y) := by simp
  rw [he,(rhombicPeriodPair t ht).weierstrassP_neg] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem rhombic_weierstrassP_imaginary_le_one {t y : ℝ} (ht : 0 < t)
    (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    ((rhombicPeriodPair t ht).weierstrassP (I*y)).re ≤
      ((rhombicPeriodPair t ht).weierstrassP 1).re := by
  have ht' : 0 < 1/t := one_div_pos.mpr ht
  have hy' : y/t ∈ Ioo (0 : ℝ) 2 :=
    ⟨div_pos hy.1 ht,(div_lt_iff₀ ht).mpr hy.2⟩
  have hg := rhombic_weierstrassP_real_ge_one ht' hy'
  have hz : (I*(y : ℂ))/(I*t) = ((y/t : ℝ) : ℂ) := by
    push_cast
    field_simp [I_ne_zero,Complex.ofReal_ne_zero.mpr ht.ne']
  have he : (rhombicPeriodPair t ht).weierstrassP (I*y) =
      -(rhombicPeriodPair (1/t) ht').weierstrassP (y/t)/(t : ℂ)^2 := by
    rw [rhombic_weierstrassP_reciprocal ht,hz]
    push_cast
    ring
  rw [he,rhombic_weierstrassP_one_reciprocal ht]
  simp only [← Complex.ofReal_pow,Complex.div_ofReal_re,Complex.neg_re]
  simpa only [Complex.ofReal_div,neg_div] using
    neg_le_neg (div_le_div_of_nonneg_right hg (sq_nonneg t))

noncomputable def axisConstant (t : ℝ) (ht : 0 < t) (a : ℝ) : ℝ :=
  (thetaEtaExpression t).re-(thetaZeta t a).re+
    (1-a)*((rhombicPeriodPair t ht).weierstrassP a).re

theorem axisConstant_integral {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    axisConstant t ht a = ∫ x : ℝ in a..1,
      ((rhombicPeriodPair t ht).weierstrassP a).re-
        ((rhombicPeriodPair t ht).weierstrassP x).re := by
  let P : ℝ → ℝ := fun x => ((rhombicPeriodPair t ht).weierstrassP x).re
  have hc : ContinuousOn P (Icc a 1) := by
    intro x hx
    exact (rhombic_weierstrassP_real_hasDerivAt_of_pos ht ht
      (ha.1.trans_le hx.1) (lt_of_le_of_lt hx.2 (by norm_num))).continuousAt.continuousWithinAt
  have hI : IntervalIntegrable P volume a 1 := hc.intervalIntegrable_of_Icc ha.2.le
  have hd (x : ℝ) (hx : x ∈ uIcc a 1) :
      HasDerivAt (fun r : ℝ => -(thetaZeta t r).re) (P x) x := by
    have hx' : x ∈ Icc a 1 := by simpa only [uIcc_of_le ha.2.le] using hx
    have hn := real_not_mem_rhombic_lattice_of_pos ht (ha.1.trans_le hx'.1)
      (lt_of_le_of_lt hx'.2 (by norm_num))
    have h := ((thetaZeta_hasDerivAt_of_pos ht ht hn).comp_ofReal).neg
    simpa only [P,Function.comp_def,Pi.neg_apply,Complex.reCLM_apply,Complex.neg_re,neg_neg] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hI
  simp only [Complex.ofReal_one,thetaZeta_one] at he
  change axisConstant t ht a = ∫ x : ℝ in a..1, P a-P x
  rw [intervalIntegral.integral_sub intervalIntegrable_const hI,
    intervalIntegral.integral_const,smul_eq_mul]
  unfold axisConstant
  dsimp [P] at he ⊢
  linarith

theorem axisConstant_pos {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) :
    0 < axisConstant t ht a := by
  rw [axisConstant_integral ht ha]
  have hc : ContinuousOn (fun x : ℝ => ((rhombicPeriodPair t ht).weierstrassP a).re-
      ((rhombicPeriodPair t ht).weierstrassP x).re) (Icc a 1) := by
    apply continuousOn_const.sub
    intro x hx
    exact (rhombic_weierstrassP_real_hasDerivAt_of_pos ht ht
      (ha.1.trans_le hx.1) (lt_of_le_of_lt hx.2 (by norm_num))).continuousAt.continuousWithinAt
  have hp (x : ℝ) (hx : x ∈ Ioc a 1) :
      0 < ((rhombicPeriodPair t ht).weierstrassP a).re-
        ((rhombicPeriodPair t ht).weierstrassP x).re := by
    exact sub_pos.mpr (rhombic_weierstrassP_strictAnti_to_one ht
      ⟨ha.1,ha.2.le⟩ ⟨ha.1.trans hx.1,hx.2⟩ hx.1)
  exact intervalIntegral.integral_pos ha.2 hc (fun x hx => (hp x hx).le)
    ⟨1,⟨ha.2.le,le_rfl⟩,hp 1 ⟨ha.2,le_rfl⟩⟩

noncomputable def axisRegularCoefficient (t : ℝ) (ht : 0 < t) (a : ℝ) (z : ℂ) : ℂ :=
  2*(thetaEtaExpression t-thetaZeta t a+(1-a)*(rhombicPeriodPair t ht).weierstrassP a)+
    (rhombicPeriodPair t ht).derivWeierstrassP a/
      ((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)

theorem axisRegularCoefficient_imaginary_pos {t a y : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) (2*t)) :
    0 < (axisRegularCoefficient t ht a (I*y)).re := by
  have he := rhombic_weierstrassP_imaginary_le_one ht hy
  have hau := rhombic_weierstrassP_strictAnti_to_one ht
    ⟨ha.1,ha.2.le⟩ (by norm_num : (1 : ℝ) ∈ Ioc 0 1) ha.2
  simp only [Complex.ofReal_one] at hau
  have hden : ((rhombicPeriodPair t ht).weierstrassP (I*y)).re-
      ((rhombicPeriodPair t ht).weierstrassP a).re < 0 := by linarith
  have hv := rhombic_weierstrassP_derivative_real_neg_of_pos ht ht ha.1 ha.2
  have hdeq : (rhombicPeriodPair t ht).weierstrassP (I*y)-
      (rhombicPeriodPair t ht).weierstrassP a =
      ((((rhombicPeriodPair t ht).weierstrassP (I*y)).re-
        ((rhombicPeriodPair t ht).weierstrassP a).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp only [Complex.sub_im,Complex.ofReal_im,rhombic_weierstrassP_imaginary_real,
        rhombic_weierstrassP_real,sub_self]
  unfold axisRegularCoefficient
  rw [hdeq]
  simp only [Complex.add_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,sub_zero,Complex.sub_re,Complex.one_re,Complex.one_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.sub_im,rhombic_weierstrassP_real,sub_self,mul_zero,
    Complex.div_ofReal_re]
  have hbase := axisConstant_pos ht ha
  unfold axisConstant at hbase
  linarith [div_pos_of_neg_of_neg hv hden]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.axisConstant_integral
#print axioms TwoAxisHelicoid.axisConstant_pos
#print axioms TwoAxisHelicoid.axisRegularCoefficient_imaginary_pos
