import TwoAxisHelicoid.OriginalCoordinatePeriods
import TwoAxisHelicoid.HorizontalParameterAnalytic

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
attribute [local irreducible] complexA thetaA complexThetaJet thetaJet

theorem originalPath_regular {t : ℝ} (ht : 0 < t) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    thetaJet t 0 (Real.pi*originalPeriodPath t s/2) ≠ 0 := by
  exact mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht _).mp
    (rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs))

theorem originalSlopingPeriod_a_analyticAt {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 2) : AnalyticAt ℝ (originalSlopingPeriod t) a := by
  let F : ℂ × ℂ → ℂ := fun p =>
    complexA (t : ℂ) p.1 (-1+p.2*(1-I*t)/2)
  have hF (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      ContDiffAt ℂ 1 F ((a : ℂ),(s : ℂ)) := by
    have hdena : complexThetaJet t 0 (Real.pi*a/2) ≠ 0 := by
      rw [complexThetaJet_ofReal]
      exact theta_vertical_denominator ht ha.1 ha.2
    have hdenz : complexThetaJet t 0 (Real.pi*originalPeriodPath t s/2) ≠ 0 := by
      rw [complexThetaJet_ofReal]
      exact originalPath_regular ht hs
    have hb := complexA_contDiffAt_one (show 0 < (t : ℂ).re from ht) hdena hdenz
    have hm : ContDiffAt ℂ 1
        (fun p : ℂ × ℂ => ((t : ℂ),p.1,-1+p.2*(1-I*t)/2)) ((a : ℂ),(s : ℂ)) := by
      fun_prop
    exact hb.comp ((a : ℂ),(s : ℂ)) hm
  have hI := complex_intervalIntegral_analyticAt (by norm_num : (-1 : ℝ) ≤ 1) hF
  have hIR : AnalyticAt ℝ (fun b : ℝ => ∫ s : ℝ in (-1)..1, F ((b : ℂ),(s : ℂ))) a :=
    (hI.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt a)
  have h : AnalyticAt ℝ (fun b : ℝ => ((1-I*t)/2)*
      (∫ s : ℝ in (-1)..1, F ((b : ℂ),(s : ℂ)))) a :=
    analyticAt_const.mul hIR
  have he : (fun b : ℝ => ((1-I*t)/2)*
      (∫ s : ℝ in (-1)..1, F ((b : ℂ),(s : ℂ)))) = originalSlopingPeriod t := by
    funext b
    simp only [F,complexA_ofReal,originalSlopingPeriod,originalPeriodPath]
  exact he ▸ h

theorem originalSlopingPeriod_t_analyticAt {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 2) :
    AnalyticAt ℝ (fun r : ℝ => originalSlopingPeriod r a) t := by
  let F : ℂ × ℂ → ℂ := fun p =>
    complexA p.1 (a : ℂ) (-1+p.2*(1-I*p.1)/2)
  have hF (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      ContDiffAt ℂ 1 F ((t : ℂ),(s : ℂ)) := by
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
  have hI := complex_intervalIntegral_analyticAt (by norm_num : (-1 : ℝ) ≤ 1) hF
  have hc : AnalyticAt ℂ (fun r : ℂ => (1-I*r)/2) (t : ℂ) :=
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div_const
  have hR : AnalyticAt ℝ (fun r : ℝ => ((1-I*r)/2)*
      (∫ s : ℝ in (-1)..1, F ((r : ℂ),(s : ℂ)))) t :=
    ((hc.mul hI).restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  simpa only [F,complexA_ofReal,originalSlopingPeriod,originalPeriodPath] using hR

theorem originalSlopingPeriod_reflect_abscissa (t a : ℝ) :
    originalSlopingPeriod t (2-a) = originalSlopingPeriod t a := by
  unfold originalSlopingPeriod
  simp_rw [thetaA_reflect_abscissa]
  rw [originalPath_negative_kernel_integral]

theorem originalSlopingPeriod_odd_derivatives_at_one (t : ℝ) (n : ℕ) :
    iteratedDeriv (2*n+1) (originalSlopingPeriod t) 1 = 0 := by
  have he : (fun a : ℝ => originalSlopingPeriod t (2-a)) = originalSlopingPeriod t :=
    funext (originalSlopingPeriod_reflect_abscissa t)
  have h := congrFun (iteratedDeriv_comp_const_sub (2*n+1) (originalSlopingPeriod t) 2) 1
  rw [he] at h
  have hn : Odd (2*n+1) := ⟨n,by omega⟩
  norm_num only [show (2-1 : ℝ)=1 by norm_num,hn.neg_one_pow,neg_one_smul] at h
  have htwo : (2 : ℂ)*iteratedDeriv (2*n+1) (originalSlopingPeriod t) 1 = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem originalSlopingPeriod_deriv_at_one (t : ℝ) :
    deriv (originalSlopingPeriod t) 1 = 0 := by
  simpa only [Nat.mul_zero,zero_add,iteratedDeriv_one] using
    originalSlopingPeriod_odd_derivatives_at_one t 0

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalSlopingPeriod_a_analyticAt
#print axioms TwoAxisHelicoid.originalSlopingPeriod_t_analyticAt
#print axioms TwoAxisHelicoid.originalSlopingPeriod_odd_derivatives_at_one
