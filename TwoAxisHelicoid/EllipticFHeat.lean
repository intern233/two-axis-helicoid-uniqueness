import TwoAxisHelicoid.ThetaLogHigher
import TwoAxisHelicoid.EllipticFGlobalDerivative

/-! The heat identity at the real half-period, for the actual elliptic functions. -/
namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaQuotient thetaLogSecond thetaLogFourth

noncomputable def ellipticC (t : ℝ) (ht : 0 < t) : ℝ :=
  (deriv (rhombicPeriodPair t ht).derivWeierstrassP 1).re

theorem thetaLogSecond_one (t : ℝ) :
    thetaLogSecond t 1 = -(Real.pi^2/4:ℂ)*thetaQuotient t 2 (Real.pi/2) := by
  simp [thetaLogSecond,thetaQuotient_one_half_pi]

theorem thetaLogSecond_one_real (t : ℝ) : thetaLogSecond t 1 = (ellipticFReal t : ℂ) := by
  rw [thetaLogSecond_one_half_series,ellipticFReal_formula]

theorem thetaLogSecond_one_parameter_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => thetaLogSecond s 1)
      ((Real.pi^3/32:ℂ)*(thetaQuotient t 2 (Real.pi/2)^2-
        thetaQuotient t 4 (Real.pi/2))) t := by
  have hz := mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht (1:ℂ)).mp
    (real_not_mem_rhombic_lattice_of_pos ht (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2))
  simp only [mul_one] at hz
  have hd := (thetaQuotient_parameter_hasDerivAt ht 2 (Real.pi/2) hz).const_mul
    (-(Real.pi^2/4:ℂ))
  convert hd using 1
  · funext s
    exact thetaLogSecond_one s
  · norm_num
    ring

theorem ellipticFReal_heat_identity {t : ℝ} (ht : 0 < t) :
    Real.pi * deriv ellipticFReal t = ellipticC t ht / 2 - ellipticFReal t ^ 2 := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (thetaLogSecond_one_parameter_hasDerivAt ht)
  change HasDerivAt ellipticFReal _ t at hd
  rw [hd.deriv]
  have hz : (1:ℂ) ∉ (rhombicPeriodPair t ht).lattice :=
    real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  have hc := thetaLogFourth_eq_weierstrassP_second ht hz
  have he : (Real.pi:ℂ)*((Real.pi^3/32:ℂ)*(thetaQuotient t 2 (Real.pi/2)^2-
        thetaQuotient t 4 (Real.pi/2))) =
      thetaLogFourth t 1/2 - thetaLogSecond t 1^2 := by
    rw [thetaLogFourth_one,thetaLogSecond_one]
    ring
  rw [hc,thetaLogSecond_one_real] at he
  have hr := congrArg Complex.re he
  change Real.pi * ((Real.pi^3/32:ℂ)*(thetaQuotient t 2 (Real.pi/2)^2-
    thetaQuotient t 4 (Real.pi/2))).re = _
  simpa only [ellipticC,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    sub_zero,Complex.sub_re,Complex.div_ofNat_re,← Complex.ofReal_pow] using hr

theorem ellipticC_pos {t : ℝ} (ht : 0 < t) : 0 < ellipticC t ht := by
  have h := ellipticFReal_heat_identity ht
  have hp := mul_pos Real.pi_pos (ellipticFReal_deriv_pos_of_pos ht)
  nlinarith [sq_nonneg (ellipticFReal t)]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_heat_identity
#print axioms TwoAxisHelicoid.ellipticC_pos
