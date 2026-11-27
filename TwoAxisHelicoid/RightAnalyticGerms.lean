import TwoAxisHelicoid.RightHeightGerm
import TwoAxisHelicoid.FullPeriodAnalytic
import TwoAxisHelicoid.HorizontalAbscissaSymmetry

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] complexA thetaA complexThetaJet thetaJet verticalA

theorem exists_right_even_analytic_germs : ∃ f g : ℝ → ℝ,
    AnalyticAt ℝ f 0 ∧ AnalyticAt ℝ g 0 ∧
    f 0 = ellipticVerticalUpper ∧ g 0 = -Real.pi/ellipticVerticalUpper ∧
    ((fun x : ℝ => f (-x)) =ᶠ[𝓝 0] f) ∧
    ((fun x : ℝ => g (-x)) =ᶠ[𝓝 0] g) ∧
    (∀ᶠ t : ℝ in 𝓝[<] ellipticVerticalUpper,
      f (verticalA t-1) = t ∧ g (verticalA t-1) = actualPeriodAlong t) := by
  obtain ⟨ψ,hψ,hψ1,heven,hreal,hactual⟩ := exists_right_height_germ
  let T := ellipticVerticalUpper
  let F : ℂ × ℂ → ℂ := fun p => complexA (ψ p.1) p.1 (p.2+I*(ψ p.1/2))
  let B : ℝ → ℝ := fun a => (1/2:ℝ)*(∫ x : ℝ in (-1)..1, F ((a:ℂ),(x:ℂ))).re
  have harg (s x : ℝ) : (x:ℂ)+I*((s:ℂ)/2) = (x:ℂ)+I*((s/2:ℝ):ℂ) := by push_cast; rfl
  have hF (x : ℝ) (_hx : x ∈ Icc (-1:ℝ) 1) : ContDiffAt ℂ 1 F (1,(x:ℂ)) := by
    have hdena : complexThetaJet (ψ 1) 0 (Real.pi*(1:ℂ)/2) ≠ 0 := by
      rw [hψ1,complexThetaJet_ofReal]
      simpa only [Complex.ofReal_one] using theta_vertical_denominator ellipticVerticalUpper_pos
        (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)
    have hdenz : complexThetaJet (ψ 1) 0 (Real.pi*((x:ℂ)+I*(ψ 1/2))/2) ≠ 0 := by
      rw [hψ1,complexThetaJet_ofReal,harg]
      exact horizontal_midline_regular ellipticVerticalUpper_pos x
    have ht : 0 < (ψ 1).re := by rw [hψ1]; exact ellipticVerticalUpper_pos
    have hbase := complexA_contDiffAt_one ht hdena hdenz
    have hb : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => ψ p.1) (1,(x:ℂ)) :=
      hψ.contDiffAt.comp (1,(x:ℂ)) contDiffAt_fst
    have hmap : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => (ψ p.1,p.1,p.2+I*(ψ p.1/2))) (1,(x:ℂ)) :=
      hb.prodMk (contDiffAt_fst.prodMk (contDiffAt_snd.add (contDiffAt_const.mul (hb.div_const 2))))
    exact hbase.comp (1,(x:ℂ)) hmap
  have hI := complex_intervalIntegral_analyticAt (by norm_num : (-1:ℝ) ≤ 1) hF
  have hIR : AnalyticAt ℝ (fun a : ℝ => ∫ x : ℝ in (-1)..1, F ((a:ℂ),(x:ℂ))) 1 := by
    have hi : AnalyticAt ℝ (fun z : ℂ => ∫ x : ℝ in (-1)..1, F (z,(x:ℂ))) (Complex.ofRealCLM 1) := by
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using hI.restrictScalars (𝕜 := ℝ)
    exact hi.comp (f := fun a : ℝ => (a:ℂ)) (x := (1:ℝ)) (Complex.ofRealCLM.analyticAt 1)
  have hRe : AnalyticAt ℝ (fun a : ℝ => (∫ x : ℝ in (-1)..1, F ((a:ℂ),(x:ℂ))).re) 1 :=
    (Complex.reCLM.analyticAt _).comp
      (f := fun a : ℝ => ∫ x : ℝ in (-1)..1, F ((a:ℂ),(x:ℂ))) hIR
  have hB : AnalyticAt ℝ B 1 := analyticAt_const.mul hRe
  have hψR : AnalyticAt ℝ (fun a : ℝ => (ψ a).re) 1 := by
    have hc : AnalyticAt ℝ (fun a : ℝ => ψ a) 1 :=
      (show AnalyticAt ℝ ψ (Complex.ofRealCLM 1) by
        simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using hψ.restrictScalars (𝕜 := ℝ)).comp
          (f := fun a : ℝ => (a:ℂ)) (x := (1:ℝ)) (Complex.ofRealCLM.analyticAt 1)
    exact (Complex.reCLM.analyticAt _).comp (f := fun a : ℝ => ψ a) hc
  have hBR (a : ℝ) (ha : (ψ a).im = 0) : B a = thetaHorizontalPeriod (ψ a).re a := by
    have he : ψ (a:ℂ) = ((ψ a).re:ℂ) := by
      apply Complex.ext <;> simp [ha]
    simp only [B,F]
    rw [he]
    simp only [harg,complexA_ofReal,thetaHorizontalPeriod,Complex.ofReal_re]
  have hcast : Tendsto (fun a : ℝ => (a:ℂ)) (𝓝 1) (𝓝 (1:ℂ)) := by
    simpa only [Complex.ofReal_one] using (Complex.continuous_ofReal.continuousAt (x := (1:ℝ))).tendsto
  have hevR : ∀ᶠ a : ℝ in 𝓝 1, ψ ((2-a:ℝ):ℂ) = ψ (a:ℂ) := by
    filter_upwards [hcast.eventually heven] with a ha
    simpa only [Complex.ofReal_sub,Complex.ofReal_ofNat] using ha
  have hBsym : ∀ᶠ a : ℝ in 𝓝 1, B (2-a) = B a := by
    have hrev : Tendsto (fun a : ℝ => 2-a) (𝓝 1) (𝓝 1) := by
      have hc : ContinuousAt (fun a : ℝ => 2-a) 1 := continuousAt_const.sub continuousAt_id
      simpa only [show (2-1:ℝ)=1 by norm_num] using hc.tendsto
    filter_upwards [hevR,hreal,hrev.eventually hreal] with a he hr hrr
    rw [hBR _ hrr,hBR _ hr,he,horizontal_period_reflect_abscissa]
  let f : ℝ → ℝ := fun x => (ψ ((1+x:ℝ):ℂ)).re
  let g : ℝ → ℝ := fun x => B (1+x)
  have hshift : AnalyticAt ℝ (fun x : ℝ => 1+x) 0 := analyticAt_const.add analyticAt_id
  have hf : AnalyticAt ℝ f 0 := by
    exact (show AnalyticAt ℝ (fun a : ℝ => (ψ a).re) (1+0) by simpa only [add_zero] using hψR).comp
      (f := fun x : ℝ => 1+x) (x := (0:ℝ)) hshift
  have hg : AnalyticAt ℝ g 0 := by
    exact (show AnalyticAt ℝ B (1+0) by simpa only [add_zero] using hB).comp
      (f := fun x : ℝ => 1+x) (x := (0:ℝ)) hshift
  have hshiftlim : Tendsto (fun x : ℝ => 1+x) (𝓝 0) (𝓝 1) := by
    simpa only [add_zero] using hshift.continuousAt.tendsto
  have hf0 : f 0 = T := by simp only [f,add_zero,Complex.ofReal_one,hψ1,Complex.ofReal_re,T]
  have hg0 : g 0 = -Real.pi/T := by
    change B (1+0) = _
    rw [add_zero,hBR 1 (by simp only [Complex.ofReal_one,hψ1,Complex.ofReal_im])]
    simp only [Complex.ofReal_one,hψ1,Complex.ofReal_re,thetaHorizontalPeriod_right_endpoint,T]
  have hfe : (fun x : ℝ => f (-x)) =ᶠ[𝓝 0] f := by
    filter_upwards [hshiftlim.eventually hevR] with x hx
    have he : 2-(1+x) = 1+ -x := by ring
    simpa only [f,he] using congrArg Complex.re hx
  have hge : (fun x : ℝ => g (-x)) =ᶠ[𝓝 0] g := by
    filter_upwards [hshiftlim.eventually hBsym] with x hx
    have he : 2-(1+x) = 1+ -x := by ring
    simpa only [g,he] using hx
  refine ⟨f,g,hf,hg,hf0,hg0,hfe,hge,?_⟩
  filter_upwards [hactual] with t ht
  have hfr : f (verticalA t-1) = t := by
    simp only [f,show 1+(verticalA t-1)=verticalA t by ring,ht,Complex.ofReal_re]
  refine ⟨hfr,?_⟩
  change B (1+(verticalA t-1)) = _
  rw [show 1+(verticalA t-1)=verticalA t by ring,hBR _ (by rw [ht]; rfl),ht]
  rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_right_even_analytic_germs
