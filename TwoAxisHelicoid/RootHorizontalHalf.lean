import TwoAxisHelicoid.ThetaADoublePeriod
import TwoAxisHelicoid.RootHorizontalRegular

namespace TwoAxisHelicoid
open Complex MeasureTheory
open scoped ComplexConjugate
attribute [local irreducible] thetaJet thetaA

theorem root_horizontal_integrand_continuous_fixed {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) (a : ℝ) :
    Continuous (fun x : ℝ => thetaA t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))) := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num [rootTLower]) htl
  rw [continuous_iff_continuousAt]
  intro x
  have harg : ContinuousAt (fun u : ℝ => (u : ℂ)+I*((t/2 : ℝ) : ℂ)) x := by fun_prop
  exact (thetaA_differentiableAt ht a (root_horizontal_regular htl htu x)).continuousAt.comp
    (f := fun u : ℝ => (u : ℂ)+I*((t/2 : ℝ) : ℂ)) harg

theorem root_horizontal_integral_halves {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (_htu : t ≤ (rootTUpper : ℝ)) (a : ℝ) :
    (∫ x : ℝ in 0..1, thetaA t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))) =
      conj (∫ x : ℝ in (-1)..0, thetaA t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))) := by
  have ht : 0 < t := lt_of_lt_of_le (by norm_num [rootTLower]) htl
  let f : ℝ → ℂ := fun x => thetaA t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))
  calc
    _ = ∫ x : ℝ in (-1)..0, f (x+1) := by
      change (∫ x : ℝ in 0..1, f x) = _
      symm
      simpa only [neg_add_cancel, zero_add] using
        intervalIntegral.integral_comp_add_right f (a := (-1 : ℝ)) (b := 0) 1
    _ = ∫ x : ℝ in (-1)..0, conj (f x) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact thetaA_midline_add_one ht a x
    _ = _ := intervalIntegral.intervalIntegral_conj

theorem root_horizontal_period_half {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) (a : ℝ) :
    thetaHorizontalPeriod t a =
      (∫ x : ℝ in (-1)..0, thetaA t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))).re := by
  have hc := root_horizontal_integrand_continuous_fixed htl htu a
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0 (μ := volume)) (hc.intervalIntegrable 0 1 (μ := volume))
  unfold thetaHorizontalPeriod
  rw [← hs, root_horizontal_integral_halves htl htu a]
  simp only [Complex.add_re, Complex.conj_re]
  ring

theorem root_horizontal_integral_real {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) (a : ℝ) :
    (∫ x : ℝ in (-1)..1, thetaA t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))).im = 0 := by
  have hc := root_horizontal_integrand_continuous_fixed htl htu a
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0 (μ := volume)) (hc.intervalIntegrable 0 1 (μ := volume)),
    root_horizontal_integral_halves htl htu a]
  simp only [Complex.add_im, Complex.conj_im, add_neg_cancel]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_horizontal_period_half
