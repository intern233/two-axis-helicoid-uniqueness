import TwoAxisHelicoid.EllipticPeriodDerivative
import TwoAxisHelicoid.WeierstrassMoments

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology
attribute [local irreducible] thetaA thetaJet complexThetaJet complexA

noncomputable def ellipticI (t : ℝ) (ht : 0 < t) : ℝ :=
  ((rhombicPeriodPair t ht).g₂/12+
    2*(rhombicPeriodPair t ht).weierstrassP 1*thetaEtaExpression t+
    (rhombicPeriodPair t ht).weierstrassP 1^2).re

theorem fullComplexWeight_a_analyticAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    AnalyticAt ℝ (fullComplexWeight t ht) a := by
  let L := rhombicPeriodPair t ht
  let F : ℂ × ℂ → ℂ := fun p => L.weierstrassP (p.2+I*((t/2:ℝ):ℂ))*
    complexA (t:ℂ) p.1 (p.2+I*((t/2:ℝ):ℂ))
  have hF (x : ℝ) (_hx : x ∈ Icc (-1:ℝ) 1) : ContDiffAt ℂ 1 F ((a:ℂ),(x:ℂ)) := by
    have hdena : complexThetaJet t 0 (Real.pi*a/2) ≠ 0 := by
      rw [complexThetaJet_ofReal]
      exact theta_vertical_denominator ht ha.1 ha.2
    have hdenz : complexThetaJet t 0 (Real.pi*((x:ℂ)+I*((t/2:ℝ):ℂ))/2) ≠ 0 := by
      rw [complexThetaJet_ofReal]
      exact horizontal_midline_regular ht x
    have hbase := complexA_contDiffAt_one (show 0 < (t:ℂ).re from ht) hdena hdenz
    have hmap : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => ((t:ℂ),p.1,p.2+I*((t/2:ℝ):ℂ))) ((a:ℂ),(x:ℂ)) := by fun_prop
    have hA := hbase.comp ((a:ℂ),(x:ℂ)) hmap
    have hP := (L.analyticOnNhd_weierstrassP _ (rhombic_midline_not_mem ht x)).contDiffAt (n := 1)
    have harg : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => p.2+I*((t/2:ℝ):ℂ)) ((a:ℂ),(x:ℂ)) := by fun_prop
    have hPC : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => L.weierstrassP (p.2+I*((t/2:ℝ):ℂ))) ((a:ℂ),(x:ℂ)) :=
      ContDiffAt.fun_comp (𝕜 := ℂ) (n := 1)
        (f := fun p : ℂ × ℂ => p.2+I*((t/2:ℝ):ℂ)) (g := L.weierstrassP)
        ((a:ℂ),(x:ℂ)) hP harg
    exact hPC.mul hA
  have hI := complex_intervalIntegral_analyticAt (by norm_num : (-1:ℝ) ≤ 1) hF
  have hIR : AnalyticAt ℝ (fun b : ℝ => ∫ x : ℝ in (-1)..1, F ((b:ℂ),(x:ℂ))) a :=
    (hI.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt a)
  have hr : AnalyticAt ℝ (fun b : ℝ => (1/2:ℂ)*(∫ x : ℝ in (-1)..1, F ((b:ℂ),(x:ℂ)))) a :=
    analyticAt_const.mul hIR
  have he : (fun b : ℝ => (1/2:ℂ)*(∫ x : ℝ in (-1)..1, F ((b:ℂ),(x:ℂ)))) = fullComplexWeight t ht := by
    funext b
    simp only [F,L,complexA_ofReal,fullComplexWeight]
  exact he ▸ hr

theorem fullComplexPeriod_one {t : ℝ} (ht : 0 < t) :
    fullComplexPeriod t 1 = -thetaEtaExpression t-(rhombicPeriodPair t ht).weierstrassP 1 := by
  have hc : Continuous (fun x : ℝ => (rhombicPeriodPair t ht).weierstrassP ((x:ℂ)+I*((t/2:ℝ):ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (rhombic_weierstrassP_hasDerivAt ht (rhombic_midline_not_mem ht x)).continuousAt.comp
      (f := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)) (by fun_prop)
  unfold fullComplexPeriod
  simp_rw [thetaA_one_eq_weierstrassP ht (rhombic_midline_not_mem ht _)]
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable (-1) 1 (μ := volume)) intervalIntegrable_const,
    weierstrass_midline_integral ht,intervalIntegral.integral_const]
  norm_num [Complex.real_smul]
  ring

theorem fullComplexWeight_one {t : ℝ} (ht : 0 < t) :
    fullComplexWeight t ht 1 = (rhombicPeriodPair t ht).g₂/12+
      (rhombicPeriodPair t ht).weierstrassP 1*thetaEtaExpression t := by
  let L := rhombicPeriodPair t ht
  let z := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)
  have hc : Continuous (fun x : ℝ => L.weierstrassP (z x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (rhombic_weierstrassP_hasDerivAt ht (rhombic_midline_not_mem ht x)).continuousAt.comp (f := z) (by fun_prop)
  have he (x : ℝ) : L.weierstrassP (z x)*thetaA t 1 (z x) =
      L.weierstrassP (z x)^2-L.weierstrassP 1*L.weierstrassP (z x) := by
    rw [thetaA_one_eq_weierstrassP ht (rhombic_midline_not_mem ht x)]
    ring
  unfold fullComplexWeight
  change (1/2:ℂ)*(∫ x : ℝ in (-1)..1, L.weierstrassP (z x)*thetaA t 1 (z x)) = _
  simp_rw [he]
  have hcsq : Continuous (fun x : ℝ => L.weierstrassP (z x)^2) := hc.pow 2
  rw [intervalIntegral.integral_sub (hcsq.intervalIntegrable (-1) 1 (μ := volume))
    ((hc.intervalIntegrable (-1) 1).const_mul (L.weierstrassP 1)),intervalIntegral.integral_const_mul]
  rw [weierstrass_midline_square_integral ht,weierstrass_midline_integral ht]
  dsimp [L]
  ring

theorem horizontalPeriodDa_hasDerivAt_one {t : ℝ} (ht : 0 < t) :
    HasDerivAt (horizontalPeriodDa t) (-2*ellipticI t ht) 1 := by
  let L := rhombicPeriodPair t ht
  let D := fun a : ℝ => 2*(thetaEtaExpression t-thetaZeta t a)*fullComplexPeriod t a-
    2*(a-1)*fullComplexWeight t ht a
  have hz : (1:ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht (by norm_num) (by norm_num)
  have hζ := (thetaZeta_hasDerivAt_of_pos ht ht hz).comp_ofReal
  have hK := (hζ.const_sub (thetaEtaExpression t)).const_mul (2:ℂ)
  have hP := fullComplexPeriod_a_hasDerivAt ht (by norm_num : (1:ℝ) ∈ Ioo 0 2)
  have hQ := (fullComplexWeight_a_analyticAt ht (by norm_num : (1:ℝ) ∈ Ioo 0 2)).differentiableAt.hasDerivAt
  have hR := (((hasDerivAt_id (1:ℝ)).ofReal_comp).sub_const (1:ℂ)).const_mul 2
  have hd := (hK.mul hP).sub (hR.mul hQ)
  have hd' : HasDerivAt D (2*L.weierstrassP 1*fullComplexPeriod t 1-2*fullComplexWeight t ht 1) 1 := by
    convert hd using 1
    · rfl
    · simp [L,id_eq,thetaZeta_one]
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 1 hd'
  have he : (horizontalPeriodDa t) =ᶠ[𝓝 (1:ℝ)] fun a => (D a).re := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)] with a ha
    have hp := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a (fullComplexPeriod_a_hasDerivAt ht ha)
    have heq : (fun b : ℝ => (fullComplexPeriod t b).re) = thetaHorizontalPeriod t := funext (fullComplexPeriod_re t)
    change HasDerivAt (fun b : ℝ => (fullComplexPeriod t b).re) (D a).re a at hp
    rw [heq] at hp
    exact (horizontal_period_a_hasDerivAt ht ha).unique hp
  have hresult := hr.congr_of_eventuallyEq he
  convert hresult using 1
  change -2*ellipticI t ht = (2*L.weierstrassP 1*fullComplexPeriod t 1-2*fullComplexWeight t ht 1).re
  rw [fullComplexPeriod_one ht,fullComplexWeight_one ht]
  unfold ellipticI
  change -2*((L.g₂/12+2*L.weierstrassP 1*thetaEtaExpression t+L.weierstrassP 1^2).re) =
    (2*L.weierstrassP 1*(-thetaEtaExpression t-L.weierstrassP 1)-
      2*(L.g₂/12+L.weierstrassP 1*thetaEtaExpression t)).re
  have he (e η g : ℂ) : 2*e*(-η-e)-2*(g/12+e*η) = -2*(g/12+2*e*η+e^2) := by ring
  rw [he]
  simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.horizontalPeriodDa_hasDerivAt_one
