import TwoAxisHelicoid.SigmaQuasiPeriods
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaZeta

theorem weierstrass_line_integrable {t : ℝ} (ht0 : 0 < t) {z w : ℂ}
    (hreg : ∀ s ∈ Icc (0:ℝ) 1, z+(s:ℂ)*w ∉ (rhombicPeriodPair t ht0).lattice) :
    IntervalIntegrable (fun s : ℝ => w*(rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)) volume 0 1 := by
  have hc : ContinuousOn (fun s : ℝ => w*(rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)) (Icc 0 1) := by
    intro s hs
    have hp := ((rhombicPeriodPair t ht0).analyticOnNhd_weierstrassP _ (hreg s hs)).continuousAt
    exact (continuousAt_const.mul (hp.comp (f := fun u : ℝ => z+(u:ℂ)*w) (by fun_prop))).continuousWithinAt
  exact hc.intervalIntegrable_of_Icc (by norm_num)

theorem weierstrass_line_integral {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {z w : ℂ}
    (hreg : ∀ s ∈ Icc (0:ℝ) 1, z+(s:ℂ)*w ∉ (rhombicPeriodPair t ht0).lattice) :
    (∫ s : ℝ in (0)..1, w*(rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)) =
      thetaZeta t z-thetaZeta t (z+w) := by
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun u : ℝ => -thetaZeta t (z+(u:ℂ)*w))
        (w*(rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)) s := by
    have harg := (((hasDerivAt_id s).ofReal_comp).mul_const w).const_add z
    have h := ((thetaZeta_hasDerivAt ht ht0 (hreg s hs)).comp s harg).neg
    convert h using 1
    · rfl
    · simp only [Complex.ofReal_one,one_mul]
      ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs))
    (weierstrass_line_integrable ht0 hreg)
  simpa only [Complex.ofReal_one,Complex.ofReal_zero,one_mul,zero_mul,add_zero,neg_sub_neg] using hFTC

noncomputable def heightLineIntegral (t : ℝ) (ht0 : 0 < t) (c u : ℝ) (z w : ℂ) : ℂ :=
  ∫ s : ℝ in (0)..1, w*(I*c*((rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)-u))

theorem heightLineIntegral_eq {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c u : ℝ) {z w : ℂ}
    (hreg : ∀ s ∈ Icc (0:ℝ) 1, z+(s:ℂ)*w ∉ (rhombicPeriodPair t ht0).lattice) :
    heightLineIntegral t ht0 c u z w =
      I*c*(thetaZeta t z-thetaZeta t (z+w)-u*w) := by
  have he (s : ℝ) : w*(I*c*((rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)-u)) =
      I*c*(w*(rhombicPeriodPair t ht0).weierstrassP (z+(s:ℂ)*w)-u*w) := by ring
  unfold heightLineIntegral
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
    (weierstrass_line_integrable ht0 hreg) intervalIntegrable_const,
    weierstrass_line_integral ht ht0 hreg]
  simp

theorem heightLineIntegral_two {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c u : ℝ) {z : ℂ}
    (hreg : ∀ s ∈ Icc (0:ℝ) 1, z+(s:ℂ)*2 ∉ (rhombicPeriodPair t ht0).lattice) :
    heightLineIntegral t ht0 c u z 2 = -2*I*c*(thetaEtaExpression t+u) := by
  rw [heightLineIntegral_eq ht ht0 c u hreg,thetaZeta_add_two]
  ring

theorem heightLineIntegral_half {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (c u : ℝ) {z : ℂ}
    (hreg : ∀ s ∈ Icc (0:ℝ) 1, z+(s:ℂ)*(1+I*t) ∉ (rhombicPeriodPair t ht0).lattice) :
    heightLineIntegral t ht0 c u z (1+I*t) =
      -I*c*((thetaEtaExpression t+u)*(1+I*t)-Real.pi*I) := by
  have hz := hreg 0 (by norm_num)
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at hz
  rw [heightLineIntegral_eq ht ht0 c u hreg,thetaZeta_add_half ht ht0 hz]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.heightLineIntegral_half
