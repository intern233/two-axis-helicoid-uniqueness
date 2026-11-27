import TwoAxisHelicoid.AxisGaussRegular

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaGauss thetaZeta thetaEtaExpression

noncomputable def axisRegularExtension (t : ℝ) (ht : 0 < t) (a : ℝ) (z : ℂ) : ℂ :=
  2*(thetaEtaExpression t-thetaZeta t a+(1-a)*(rhombicPeriodPair t ht).weierstrassP a)+
    (rhombicPeriodPair t ht).derivWeierstrassP a*z^2/
      (1+z^2*((rhombicPeriodPair t ht).weierstrassPExcept 0 z-
        (rhombicPeriodPair t ht).weierstrassP a))

theorem axisRegularExtension_eq {t : ℝ} (ht : 0 < t) (a : ℝ) {z : ℂ}
    (hz : z ≠ 0) : axisRegularExtension t ht a z = axisRegularCoefficient t ht a z := by
  let L := rhombicPeriodPair t ht
  have hP : L.weierstrassPExcept 0 z+1/z^2 = L.weierstrassP z := by
    simpa using L.weierstrassPExcept_add (0 : L.lattice) z
  have he : 1+z^2*(L.weierstrassPExcept 0 z-L.weierstrassP a) =
      (L.weierstrassP z-L.weierstrassP a)*z^2 := by
    rw [← hP]
    field_simp
    ring
  unfold axisRegularExtension axisRegularCoefficient
  change _+L.derivWeierstrassP a*z^2/(1+z^2*(L.weierstrassPExcept 0 z-L.weierstrassP a)) = _
  rw [he,mul_div_mul_right _ _ (pow_ne_zero 2 hz)]

theorem axisRegularExtension_analyticAt_zero {t : ℝ} (ht : 0 < t) (a : ℝ) :
    AnalyticAt ℂ (axisRegularExtension t ht a) 0 := by
  let L := rhombicPeriodPair t ht
  have hP : AnalyticAt ℂ (fun z : ℂ => L.weierstrassPExcept 0 z-L.weierstrassP a) 0 :=
    (L.analyticAt_weierstrassPExcept 0).sub analyticAt_const
  have hn : AnalyticAt ℂ (fun z : ℂ => L.derivWeierstrassP a*z^2) 0 :=
    analyticAt_const.mul (analyticAt_id.pow 2)
  have hd : AnalyticAt ℂ (fun z : ℂ => 1+z^2*(L.weierstrassPExcept 0 z-L.weierstrassP a)) 0 :=
    analyticAt_const.add ((analyticAt_id.pow 2).mul hP)
  exact analyticAt_const.add (hn.div hd (by simp))

theorem axisRegularExtension_zero {t : ℝ} (ht : 0 < t) (a : ℝ) :
    axisRegularExtension t ht a 0 =
      2*(thetaEtaExpression t-thetaZeta t a+(1-a)*(rhombicPeriodPair t ht).weierstrassP a) := by
  simp only [axisRegularExtension,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,zero_mul,
    add_zero,zero_div]

theorem axisRegularExtension_zero_re_pos {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) : 0 < (axisRegularExtension t ht a 0).re := by
  rw [axisRegularExtension_zero]
  have hp := axisConstant_pos ht ha
  unfold axisConstant at hp
  simp only [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.sub_im,
    Complex.re_ofNat,Complex.im_ofNat,Complex.one_re,Complex.one_im,Complex.ofReal_re,
    Complex.ofReal_im,rhombic_weierstrassP_real,zero_mul,mul_zero,sub_self,sub_zero]
  linarith

theorem actualGauss_end_holomorphic_extension {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∀ z, z ∉ (rhombicPeriodPair t ht).lattice →
        z-a ∉ (rhombicPeriodPair t ht).lattice →
        z+a ∉ (rhombicPeriodPair t ht).lattice →
        deriv (thetaGauss t a 1) z/thetaGauss t a 1 z-
          I*((2*(a-1)/c : ℝ) : ℂ)*(coordinateData t a c ht z 2) = q z := by
  refine ⟨axisRegularExtension t ht a,axisRegularExtension_analyticAt_zero ht a,?_⟩
  intro z hz hm hp
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (zero_mem _)
  rw [actualGauss_end_regular_coefficient ht ha hc hz hm hp,axisRegularExtension_eq ht a hz0]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualGauss_end_holomorphic_extension
