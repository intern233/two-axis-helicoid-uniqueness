import TwoAxisHelicoid.OriginalComplexPeriodHeat
import TwoAxisHelicoid.VerticalBranchAnalytic

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] complexA thetaA complexThetaJet thetaJet verticalA
  thetaLt thetaLz thetaLa

noncomputable def originalComplexPeriodAlong (t : ℝ) : ℂ :=
  originalSlopingPeriod t (verticalA t)

theorem original_branch_kernel_C1 {t s : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper)
    {ψ : ℂ → ℂ} (hψ : AnalyticAt ℂ ψ (t : ℂ))
    (hψt : ψ (t : ℂ) = (verticalA t : ℂ)) (hs : s ∈ Icc (-1 : ℝ) 1) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ =>
      complexA p.1 (ψ p.1) (-1+p.2*(1-I*p.1)/2)) ((t : ℂ),(s : ℂ)) := by
  have ha := (verticalA_spec ht).1
  have hdena : complexThetaJet t 0 (Real.pi*ψ t/2) ≠ 0 := by
    rw [hψt,complexThetaJet_ofReal]
    exact theta_vertical_denominator ht.1 ha.1 (by linarith [ha.2])
  have hdenz : complexThetaJet t 0 (Real.pi*originalPeriodPath t s/2) ≠ 0 := by
    rw [complexThetaJet_ofReal]
    exact originalPath_regular ht.1 hs
  have hb := complexA_contDiffAt_one (show 0 < (t : ℂ).re from ht.1) hdena hdenz
  have hp : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => ψ p.1) ((t : ℂ),(s : ℂ)) :=
    hψ.contDiffAt.comp ((t : ℂ),(s : ℂ)) contDiffAt_fst
  have hm : ContDiffAt ℂ 1 (fun p : ℂ × ℂ =>
      (p.1,ψ p.1,-1+p.2*(1-I*p.1)/2)) ((t : ℂ),(s : ℂ)) :=
    contDiffAt_fst.prodMk (hp.prodMk (by fun_prop))
  exact hb.comp ((t : ℂ),(s : ℂ)) hm

theorem originalComplexPeriodAlong_analyticAt {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    AnalyticAt ℝ originalComplexPeriodAlong t := by
  obtain ⟨ψ,hψ,he⟩ := verticalA_complex_germ ht
  let F : ℂ × ℂ → ℂ := fun p => complexA p.1 (ψ p.1) (-1+p.2*(1-I*p.1)/2)
  have hF (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      ContDiffAt ℂ 1 F ((t : ℂ),(s : ℂ)) :=
    original_branch_kernel_C1 ht hψ he.self_of_nhds hs
  have hI := complex_intervalIntegral_analyticAt (by norm_num : (-1 : ℝ) ≤ 1) hF
  have hq : AnalyticAt ℂ (fun r : ℂ => (1-I*r)/2) (t : ℂ) :=
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div_const
  have hR : AnalyticAt ℝ (fun r : ℝ => ((1-I*r)/2)*
      (∫ s : ℝ in (-1)..1, F ((r : ℂ),(s : ℂ)))) t :=
    ((hq.mul hI).restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  apply hR.congr
  filter_upwards [he] with r hr
  simp only [F,hr,complexA_ofReal,originalComplexPeriodAlong,
    originalSlopingPeriod,originalPeriodPath]

theorem originalTimeIntegrand_continuousOn {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (originalTimeIntegrand t a) (Icc (-1 : ℝ) 1) := by
  have hc := originalPath_fixed_time_continuousOn ht ha
  have hD := originalPath_derivative_continuousOn ht a
  have hh : ContinuousOn (fun s : ℝ => (I/2)*((s : ℂ)*
      deriv (thetaA t a) (originalPeriodPath t s))) (Icc (-1 : ℝ) 1) := by
    exact continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.mul hD)
  apply (hc.sub hh).congr
  intro s hs
  change originalTimeIntegrand t a s = thetaA t a (originalPeriodPath t s)*
    thetaLt t a (originalPeriodPath t s)-(I/2)*((s : ℂ)*deriv (thetaA t a) (originalPeriodPath t s))
  rw [thetaA_spatial_deriv ht a
    (theta_vertical_denominator ht ha.1 (by linarith [ha.2]))
    (originalPath_regular ht hs) (originalPath_shift_regular ht ha hs)]
  unfold originalTimeIntegrand
  ring

theorem originalBranchKernel_hasDerivAt_integral {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    HasDerivAt (fun r : ℝ => ∫ s : ℝ in (-1)..1,
      thetaA r (verticalA r) (originalPeriodPath r s))
      ((∫ s : ℝ in (-1)..1, originalTimeIntegrand t (verticalA t) s)+
        ((deriv verticalA t : ℝ) : ℂ)*(∫ s : ℝ in (-1)..1,
          thetaAa t (verticalA t) (originalPeriodPath t s))) t := by
  obtain ⟨ψ,hψ,he⟩ := verticalA_complex_germ ht
  have ha := (verticalA_spec ht).1
  let F : ℂ × ℂ → ℂ := fun p => complexA p.1 (ψ p.1) (-1+p.2*(1-I*p.1)/2)
  let D : ℝ → ℂ := fun s => originalTimeIntegrand t (verticalA t) s+
    ((deriv verticalA t : ℝ) : ℂ)*thetaAa t (verticalA t) (originalPeriodPath t s)
  have hF (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      ContDiffAt ℂ 1 F ((t : ℂ),(s : ℂ)) :=
    original_branch_kernel_C1 ht hψ he.self_of_nhds hs
  have hD (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      HasDerivAt (fun r : ℝ => F ((r : ℂ),(s : ℂ))) (D s) t := by
    have hd := thetaA_curve_hasDerivAt (hasDerivAt_id t)
      (verticalA_hasDerivAt ht).differentiableAt.hasDerivAt
      (originalPeriodPath_time_hasDerivAt t s) ht.1
      (thetaJet_one_at_zero_ne_zero_of_pos ht.1)
      (theta_vertical_denominator ht.1 ha.1 (by linarith [ha.2]))
      (originalPath_regular ht.1 hs) (originalPath_shift_regular ht.1 ha hs)
    have hd' : HasDerivAt (fun r : ℝ => thetaA r (verticalA r) (originalPeriodPath r s))
        (D s) t := by
      convert hd using 1
      · rfl
      · simp only [D,originalTimeIntegrand,thetaAa,id_eq,Complex.ofReal_one,one_mul]
        ring
    apply hd'.congr_of_eventuallyEq
    filter_upwards [he] with r hr
    simp only [F,hr,complexA_ofReal,originalPeriodPath]
  have hi := real_intervalIntegral_hasDerivAt_of_complex_C1
    (by norm_num : (-1 : ℝ) ≤ 1) hF hD
  have hcAa : ContinuousOn (fun s : ℝ => thetaAa t (verticalA t)
      (originalPeriodPath t s)) (Icc (-1 : ℝ) 1) :=
    thetaAa_comp_continuousOn (u := fun _ => t) (b := fun _ => verticalA t)
      continuousOn_const continuousOn_const (by unfold originalPeriodPath; fun_prop)
      (fun _ _ => ht.1)
      (fun _ _ => theta_vertical_denominator ht.1 ha.1 (by linarith [ha.2]))
      (fun _ hs => originalPath_regular ht.1 hs)
      (fun _ hs => originalPath_shift_regular ht.1 ha hs)
  have hIt := (originalTimeIntegrand_continuousOn ht.1 ha).intervalIntegrable_of_Icc
    (by norm_num : (-1 : ℝ) ≤ 1) (μ := volume)
  have hIa := hcAa.intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1) (μ := volume)
  dsimp [D] at hi
  rw [intervalIntegral.integral_add hIt (hIa.const_mul _),
    intervalIntegral.integral_const_mul] at hi
  apply hi.congr_of_eventuallyEq
  filter_upwards [he] with r hr
  simp only [F,hr,complexA_ofReal,originalPeriodPath]

theorem originalComplexPeriodAlong_hasDerivAt {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    HasDerivAt originalComplexPeriodAlong
      (deriv (fun r : ℝ => originalSlopingPeriod r (verticalA t)) t+
        ((deriv verticalA t : ℝ) : ℂ)*deriv (originalSlopingPeriod t) (verticalA t)) t := by
  have hq : HasDerivAt (fun r : ℝ => (1-I*r)/2) (-I/2) t := by
    convert ((((hasDerivAt_id t).ofReal_comp).const_mul I).const_sub 1).div_const 2 using 1 <;> simp
  have hd := hq.mul (originalBranchKernel_hasDerivAt_integral ht)
  rw [(originalSlopingPeriod_t_hasDerivAt_raw ht.1 (verticalA_spec ht).1).deriv,
    (originalSlopingPeriod_a_hasDerivAt_integral ht.1 (verticalA_spec ht).1).deriv]
  convert hd using 1
  · rfl
  · unfold slopingIntegral
    ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalComplexPeriodAlong_analyticAt
#print axioms TwoAxisHelicoid.originalComplexPeriodAlong_hasDerivAt
