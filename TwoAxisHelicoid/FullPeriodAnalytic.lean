import TwoAxisHelicoid.ComplexHorizontalFunction
import TwoAxisHelicoid.ComplexParametricIntegral
import TwoAxisHelicoid.VerticalBranchAnalytic
import TwoAxisHelicoid.FullPeriodBranch

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] complexA thetaA complexThetaJet thetaJet verticalA

theorem actualPeriodAlong_analyticAt {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    AnalyticAt ℝ actualPeriodAlong t := by
  obtain ⟨ψ,hψ,he⟩ := verticalA_complex_germ ht
  have hψt : ψ (t:ℂ) = (verticalA t:ℂ) := he.self_of_nhds
  have ha := (verticalA_spec ht).1
  let F : ℂ × ℂ → ℂ := fun p => complexA p.1 (ψ p.1) (p.2+I*(p.1/2))
  have harg (s x : ℝ) : (x:ℂ)+I*((s:ℂ)/2) = (x:ℂ)+I*((s/2:ℝ):ℂ) := by push_cast; rfl
  have hF (x : ℝ) (_hx : x ∈ Icc (-1:ℝ) 1) : ContDiffAt ℂ 1 F ((t:ℂ),(x:ℂ)) := by
    have hdena : complexThetaJet t 0 (Real.pi*ψ t/2) ≠ 0 := by
      rw [hψt,complexThetaJet_ofReal]
      exact theta_vertical_denominator ht.1 ha.1 (by linarith [ha.2])
    have hdenz : complexThetaJet t 0 (Real.pi*((x:ℂ)+I*((t:ℂ)/2))/2) ≠ 0 := by
      rw [complexThetaJet_ofReal,harg]
      exact horizontal_midline_regular ht.1 x
    have hbase := complexA_contDiffAt_one (show 0 < (t:ℂ).re from ht.1) hdena hdenz
    have hb : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => ψ p.1) ((t:ℂ),(x:ℂ)) :=
      hψ.contDiffAt.comp ((t:ℂ),(x:ℂ)) contDiffAt_fst
    have hmap : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => (p.1,ψ p.1,p.2+I*(p.1/2))) ((t:ℂ),(x:ℂ)) :=
      contDiffAt_fst.prodMk (hb.prodMk (by fun_prop))
    exact hbase.comp ((t:ℂ),(x:ℂ)) hmap
  have hI := complex_intervalIntegral_analyticAt (by norm_num : (-1:ℝ) ≤ 1) hF
  have hIR : AnalyticAt ℝ (fun s : ℝ => ∫ x : ℝ in (-1)..1, F ((s:ℂ),(x:ℂ))) t :=
    (hI.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have hRe : AnalyticAt ℝ (fun s : ℝ => (∫ x : ℝ in (-1)..1, F ((s:ℂ),(x:ℂ))).re) t :=
    (Complex.reCLM.analyticAt _).comp
      (f := fun s : ℝ => ∫ x : ℝ in (-1)..1, F ((s:ℂ),(x:ℂ))) hIR
  have hr : AnalyticAt ℝ (fun s : ℝ => (1/2:ℝ)*(∫ x : ℝ in (-1)..1, F ((s:ℂ),(x:ℂ))).re) t :=
    analyticAt_const.mul hRe
  apply hr.congr
  filter_upwards [he] with s hs
  simp only [F,hs,harg,complexA_ofReal,actualPeriodAlong,thetaHorizontalPeriod]

theorem actualPeriodAlong_analyticOnNhd :
    AnalyticOnNhd ℝ actualPeriodAlong (Ioo (0:ℝ) ellipticVerticalUpper) :=
  fun _ ht => actualPeriodAlong_analyticAt ht

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_analyticOnNhd
