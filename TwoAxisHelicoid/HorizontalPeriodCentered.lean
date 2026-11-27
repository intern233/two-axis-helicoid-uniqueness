import TwoAxisHelicoid.AllHorizontalRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace TwoAxisHelicoid
open Complex MeasureTheory
attribute [local irreducible] thetaA

theorem horizontal_real_integrand_period_one {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Function.Periodic (fun x : ℝ => (thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re) 1 := by
  intro x
  change (thetaA t a (((x+1:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re =
    (thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re
  rw [thetaA_midline_add_one ht a x,Complex.conj_re]

theorem horizontal_period_centered {t : ℝ} (ht : 0 < t) (a : ℝ) :
    thetaHorizontalPeriod t a =
      (∫ x : ℝ in (-1/2)..(1/2), thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re := by
  have hc := horizontal_integrand_continuous ht a
  have h := (horizontal_real_integrand_period_one ht a).intervalIntegral_add_eq (-1) (-1/2)
  norm_num only [neg_add_cancel,show (-1/2:ℝ)+1 = 1/2 by norm_num] at h
  have hre (b d : ℝ) :
      (∫ x : ℝ in b..d, thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re =
        ∫ x : ℝ in b..d, (thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re :=
    (Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable b d (μ := volume))).symm
  rw [horizontal_period_half ht a]
  rw [hre,hre]
  simpa only [neg_div] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_period_centered
