import TwoAxisHelicoid.OriginalPeriodRegularity
import TwoAxisHelicoid.ComplexParametricIntegralDerivative

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] thetaJet thetaA thetaLt thetaLz complexA

noncomputable def originalTimeIntegrand (t a s : ℝ) : ℂ :=
  thetaA t a (originalPeriodPath t s)*
    (thetaLt t a (originalPeriodPath t s)-
      ((s : ℂ)*I/2)*thetaLz t a (originalPeriodPath t s))

theorem originalPeriodPath_time_hasDerivAt (t s : ℝ) :
    HasDerivAt (fun r : ℝ => originalPeriodPath r s) (-(s : ℂ)*I/2) t := by
  convert ((((((hasDerivAt_id t).ofReal_comp).const_mul I).const_sub 1).const_mul (s : ℂ)).div_const 2).const_add (-1 : ℂ) using 1
  · rfl
  · simp

theorem originalTimeIntegrand_hasDerivAt {t a s : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => thetaA r a (originalPeriodPath r s))
      (originalTimeIntegrand t a s) t := by
  have hd := thetaA_curve_hasDerivAt (hasDerivAt_id t) (hasDerivAt_const t a)
    (originalPeriodPath_time_hasDerivAt t s) ht (thetaJet_one_at_zero_ne_zero_of_pos ht)
    (theta_vertical_denominator ht ha.1 (by linarith [ha.2]))
    (originalPath_regular ht hs) (originalPath_shift_regular ht ha hs)
  convert hd using 1
  · rfl
  · simp only [originalTimeIntegrand,id_eq,Complex.ofReal_one,Complex.ofReal_zero,
      one_mul,zero_mul,add_zero]
    ring

theorem original_time_kernel_C1 {t a s : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 2) (hs : s ∈ Icc (-1 : ℝ) 1) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ => complexA p.1 (a : ℂ)
      (-1+p.2*(1-I*p.1)/2)) ((t : ℂ),(s : ℂ)) := by
  have hdena : complexThetaJet t 0 (Real.pi*a/2) ≠ 0 := by
    rw [complexThetaJet_ofReal]
    exact theta_vertical_denominator ht ha.1 ha.2
  have hdenz : complexThetaJet t 0 (Real.pi*originalPeriodPath t s/2) ≠ 0 := by
    rw [complexThetaJet_ofReal]
    exact originalPath_regular ht hs
  have hb := complexA_contDiffAt_one (show 0 < (t : ℂ).re from ht) hdena hdenz
  have hm : ContDiffAt ℂ 1
      (fun p : ℂ × ℂ => (p.1,(a : ℂ),-1+p.2*(1-I*p.1)/2)) ((t : ℂ),(s : ℂ)) := by
    fun_prop
  exact hb.comp ((t : ℂ),(s : ℂ)) hm

theorem originalKernel_t_hasDerivAt_integral {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => ∫ s : ℝ in (-1)..1, thetaA r a (originalPeriodPath r s))
      (∫ s : ℝ in (-1)..1, originalTimeIntegrand t a s) t := by
  let F : ℂ × ℂ → ℂ := fun p => complexA p.1 (a : ℂ) (-1+p.2*(1-I*p.1)/2)
  have hF (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) : ContDiffAt ℂ 1 F ((t : ℂ),(s : ℂ)) :=
    original_time_kernel_C1 ht ⟨ha.1,by linarith [ha.2]⟩ hs
  have hD (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      HasDerivAt (fun r : ℝ => F ((r : ℂ),(s : ℂ))) (originalTimeIntegrand t a s) t := by
    simpa only [F,complexA_ofReal,originalPeriodPath] using originalTimeIntegrand_hasDerivAt ht ha hs
  have hi := real_intervalIntegral_hasDerivAt_of_complex_C1
    (by norm_num : (-1 : ℝ) ≤ 1) hF hD
  simpa only [F,complexA_ofReal,originalPeriodPath] using hi

theorem originalSlopingPeriod_t_hasDerivAt_raw {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => originalSlopingPeriod r a)
      ((-I/2)*(∫ s : ℝ in (-1)..1, thetaA t a (originalPeriodPath t s))+
        ((1-I*t)/2)*(∫ s : ℝ in (-1)..1, originalTimeIntegrand t a s)) t := by
  have hq : HasDerivAt (fun r : ℝ => (1-I*r)/2) (-I/2) t := by
    convert ((((hasDerivAt_id t).ofReal_comp).const_mul I).const_sub 1).div_const 2 using 1 <;> simp
  exact hq.mul (originalKernel_t_hasDerivAt_integral ht ha)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalSlopingPeriod_t_hasDerivAt_raw
