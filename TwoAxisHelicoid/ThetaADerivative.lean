import TwoAxisHelicoid.ThetaPeriod

/-! Partial derivatives of the concrete normalized horizontal differential (8.2). -/

namespace TwoAxisHelicoid
open Complex

noncomputable def thetaLa (t a : ℝ) (z : ℂ) : ℂ :=
  Real.pi * (thetaQuotient t 1 (Real.pi*z/2) -
    thetaQuotient t 1 (Real.pi*(z-a)/2) - thetaQuotient t 1 (Real.pi*a/2))

noncomputable def thetaLt (t a : ℝ) (z : ℂ) : ℂ :=
  (Real.pi/4 : ℂ) * (thetaJet t 3 0 / thetaJet t 1 0 -
    thetaQuotient t 2 (Real.pi*a/2) + thetaQuotient t 2 (Real.pi*(z-a)/2) -
    thetaQuotient t 2 (Real.pi*z/2)) +
  ((a-1)*Real.pi^2/8 : ℂ) * (thetaQuotient t 3 (Real.pi*z/2) -
    thetaQuotient t 1 (Real.pi*z/2)*thetaQuotient t 2 (Real.pi*z/2))

theorem thetaA_a_hasDerivAt {t : ℝ} (ht : 0 < t) (a : ℝ) (z : ℂ)
    (ha : thetaJet t 0 (Real.pi*a/2) ≠ 0)
    (hz : thetaJet t 0 (Real.pi*z/2) ≠ 0)
    (hm : thetaJet t 0 (Real.pi*(z-a)/2) ≠ 0) :
    HasDerivAt (fun b : ℝ => thetaA t b z) (thetaA t a z * thetaLa t a z) a := by
  have hargA : HasDerivAt (fun b : ℝ => (Real.pi*b/2 : ℂ)) (Real.pi/2 : ℂ) a := by
    convert (((hasDerivAt_id a).ofReal_comp).const_mul (Real.pi : ℂ)).div_const 2 using 1 <;>
      simp
  have hargM : HasDerivAt (fun b : ℝ => (Real.pi*(z-b)/2 : ℂ)) (-Real.pi/2 : ℂ) a := by
    convert ((((hasDerivAt_id a).ofReal_comp).const_sub z).const_mul
      (Real.pi : ℂ)).div_const 2 using 1 <;> simp
  have hdA := (thetaJet_hasDerivAt ht 0 (Real.pi*a/2)).comp a hargA
  have hdM := (thetaJet_hasDerivAt ht 0 (Real.pi*(z-a)/2)).comp a hargM
  have hp := ((hasDerivAt_const a ((Real.pi : ℂ)*thetaJet t 1 0)).div
    (hdA.const_mul 2) (mul_ne_zero (by norm_num) ha)).pow 2
  have hc := (hdM.div (hasDerivAt_const a (thetaJet t 0 (Real.pi*z/2))) hz).pow 2
  have he := (((((hasDerivAt_id a).ofReal_comp).sub_const 1).mul_const
    (Real.pi : ℂ)).mul_const (thetaQuotient t 1 (Real.pi*z/2))).cexp
  have hd := (hp.mul hc).mul he
  convert hd using 1
  · rfl
  · simp [thetaA, thetaLa, thetaQuotient]
    field_simp
    ring

theorem thetaA_parameter_hasDerivAt {t : ℝ} (ht : 0 < t) (a : ℝ) (z : ℂ)
    (hzero : thetaJet t 1 0 ≠ 0)
    (ha : thetaJet t 0 (Real.pi*a/2) ≠ 0)
    (hz : thetaJet t 0 (Real.pi*z/2) ≠ 0)
    (hm : thetaJet t 0 (Real.pi*(z-a)/2) ≠ 0) :
    HasDerivAt (fun s : ℝ => thetaA s a z) (thetaA t a z * thetaLt t a z) t := by
  have hd0 := thetaJet_parameter_hasDerivAt ht 1 0
  have hdA := thetaJet_parameter_hasDerivAt ht 0 (Real.pi*a/2)
  have hdZ := thetaJet_parameter_hasDerivAt ht 0 (Real.pi*z/2)
  have hdM := thetaJet_parameter_hasDerivAt ht 0 (Real.pi*(z-a)/2)
  have hp := ((hd0.const_mul (Real.pi : ℂ)).div
    (hdA.const_mul 2) (mul_ne_zero (by norm_num) ha)).pow 2
  have hc := (hdM.div hdZ hz).pow 2
  have he := ((thetaQuotient_parameter_hasDerivAt ht 1 (Real.pi*z/2) hz).const_mul
    ((a-1)*Real.pi : ℂ)).cexp
  have hd := (hp.mul hc).mul he
  convert hd using 1
  · rfl
  · simp [thetaA, thetaLt, thetaQuotient]
    field_simp
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_a_hasDerivAt
#print axioms TwoAxisHelicoid.thetaA_parameter_hasDerivAt
