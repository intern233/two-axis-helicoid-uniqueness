import TwoAxisHelicoid.ComplexHorizontalFunction
import TwoAxisHelicoid.ComplexParametricIntegral
import TwoAxisHelicoid.HorizontalAbscissaSymmetry
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] complexA thetaA complexThetaJet thetaJet

theorem horizontal_period_a_analyticAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    AnalyticAt ℝ (thetaHorizontalPeriod t) a := by
  let F : ℂ × ℂ → ℂ := fun p => complexA (t:ℂ) p.1 (p.2+I*((t/2:ℝ):ℂ))
  have hF (x : ℝ) (_hx : x ∈ Icc (-1:ℝ) 1) : ContDiffAt ℂ 1 F ((a:ℂ),(x:ℂ)) := by
    have hdena : complexThetaJet t 0 (Real.pi*a/2) ≠ 0 := by
      rw [complexThetaJet_ofReal]
      exact theta_vertical_denominator ht ha.1 ha.2
    have hdenz : complexThetaJet t 0 (Real.pi*((x:ℂ)+I*((t/2:ℝ):ℂ))/2) ≠ 0 := by
      rw [complexThetaJet_ofReal]
      exact horizontal_midline_regular ht x
    have hbase := complexA_contDiffAt_one (show 0 < (t:ℂ).re from ht) hdena hdenz
    have hmap : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => ((t:ℂ),p.1,p.2+I*((t/2:ℝ):ℂ))) ((a:ℂ),(x:ℂ)) := by
      fun_prop
    exact hbase.comp ((a:ℂ),(x:ℂ)) hmap
  have hI := complex_intervalIntegral_analyticAt (by norm_num : (-1:ℝ) ≤ 1) hF
  have hIR : AnalyticAt ℝ (fun b : ℝ => ∫ x : ℝ in (-1)..1, F ((b:ℂ),(x:ℂ))) a :=
    (hI.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt a)
  have hRe : AnalyticAt ℝ (fun b : ℝ => (∫ x : ℝ in (-1)..1, F ((b:ℂ),(x:ℂ))).re) a :=
    (Complex.reCLM.analyticAt _).comp
      (f := fun b : ℝ => ∫ x : ℝ in (-1)..1, F ((b:ℂ),(x:ℂ))) hIR
  have hr : AnalyticAt ℝ (fun b : ℝ => (1/2:ℝ)*(∫ x : ℝ in (-1)..1, F ((b:ℂ),(x:ℂ))).re) a :=
    analyticAt_const.mul hRe
  have he : (fun b : ℝ => (1/2:ℝ)*(∫ x : ℝ in (-1)..1, F ((b:ℂ),(x:ℂ))).re) =
      thetaHorizontalPeriod t := by
    funext b
    simp only [F,complexA_ofReal,thetaHorizontalPeriod]
  exact he ▸ hr

theorem horizontal_period_a_analyticOnNhd {t : ℝ} (ht : 0 < t) :
    AnalyticOnNhd ℝ (thetaHorizontalPeriod t) (Ioo (0:ℝ) 2) :=
  fun _ ha => horizontal_period_a_analyticAt ht ha

theorem horizontal_period_odd_derivatives_at_one (t : ℝ) (n : ℕ) :
    iteratedDeriv (2*n+1) (thetaHorizontalPeriod t) 1 = 0 := by
  have he : (fun a : ℝ => thetaHorizontalPeriod t (2-a)) = thetaHorizontalPeriod t :=
    funext (horizontal_period_reflect_abscissa t)
  have h := congrFun (iteratedDeriv_comp_const_sub (2*n+1) (thetaHorizontalPeriod t) 2) 1
  rw [he] at h
  have hn : Odd (2*n+1) := ⟨n,by omega⟩
  norm_num only [show (2-1:ℝ)=1 by norm_num,hn.neg_one_pow,neg_one_smul] at h
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontal_period_a_analyticOnNhd
#print axioms TwoAxisHelicoid.horizontal_period_odd_derivatives_at_one
