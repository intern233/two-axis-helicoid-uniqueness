import TwoAxisHelicoid.OriginalSigmaPeriodDerivative
import TwoAxisHelicoid.HorizontalRightDerivative
import TwoAxisHelicoid.GaussPrincipalParts

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval
attribute [local irreducible] complexA thetaA complexThetaJet thetaJet thetaZeta originalSigmaPeriod

/-- Analytic dependence of the actual complex weighted period on the moving
divisor, including the half-period at which the numerator can vanish on the path. -/
theorem originalComplexWeight_a_analyticAt {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 2) : AnalyticAt ℝ (originalComplexWeight t ht) a := by
  let L := rhombicPeriodPair t ht
  let z : ℂ → ℂ := fun s => -1+s*(1-I*t)/2
  let F : ℂ × ℂ → ℂ := fun p => L.weierstrassP (z p.2)*complexA (t:ℂ) p.1 (z p.2)
  have hF (s : ℝ) (hs : s ∈ Icc (-1:ℝ) 1) : ContDiffAt ℂ 1 F ((a:ℂ),(s:ℂ)) := by
    have hdena : complexThetaJet t 0 (Real.pi*a/2) ≠ 0 := by
      rw [complexThetaJet_ofReal]
      exact theta_vertical_denominator ht ha.1 ha.2
    have hdenz : complexThetaJet t 0 (Real.pi*z s/2) ≠ 0 := by
      rw [complexThetaJet_ofReal]
      exact originalPath_regular ht hs
    have hA := complexA_contDiffAt_one (show 0 < (t:ℂ).re from ht) hdena hdenz
    have arg : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => ((t:ℂ),p.1,z p.2)) ((a:ℂ),(s:ℂ)) := by
      dsimp [z]; fun_prop
    have hP : ContDiffAt ℂ 1 L.weierstrassP (z (s : ℂ)) := (L.analyticOnNhd_weierstrassP (z (s : ℂ))
      (rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs))).contDiffAt (n := 1)
    have path : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => z p.2) ((a:ℂ),(s:ℂ)) := by
      dsimp [z]; fun_prop
    exact (hP.comp ((a:ℂ),(s:ℂ)) path).mul (hA.comp ((a:ℂ),(s:ℂ)) arg)
  have integral := complex_intervalIntegral_analyticAt (by norm_num : (-1:ℝ) ≤ 1) hF
  have realIntegral : AnalyticAt ℝ (fun b : ℝ => ∫ s : ℝ in (-1)..1, F ((b:ℂ),(s:ℂ))) a :=
    (integral.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt a)
  have result := (analyticAt_const (v := ((1-I*t)/2:ℂ))).mul realIntegral
  change AnalyticAt ℝ (fun b : ℝ => ((1-I*t)/2) *
    ∫ s : ℝ in (-1)..1, L.weierstrassP (z s) * thetaA t b (z s)) a
  simpa only [F,complexA_ofReal,Pi.mul_def] using result

/-- The first parameter derivative formula extended across a=1 as an equality
of analytic germs. No division by the vanishing numerator is made at a=1. -/
private theorem sloping_deriv_germ_at_one {t : ℝ} (ht : 0<t) :
    deriv (originalSlopingPeriod t) =ᶠ[𝓝 (1:ℝ)] fun a =>
      2*(thetaEtaExpression t-thetaZeta t a)*originalSlopingPeriod t a-
        2*((a:ℂ)-1)*originalComplexWeight t ht a := by
  let D : ℝ → ℂ := fun a => 2*(thetaEtaExpression t-thetaZeta t a)*originalSlopingPeriod t a-
    2*((a:ℂ)-1)*originalComplexWeight t ht a
  have P : AnalyticOnNhd ℝ (originalSlopingPeriod t) (Ioo (0:ℝ) 2) :=
    fun _ h => originalSlopingPeriod_a_analyticAt ht h
  have rhs : AnalyticOnNhd ℝ D (Ioo (0:ℝ) 2) := by
    intro a ha
    have zeta := ((thetaZeta_analyticAt_of_pos ht
      (real_not_mem_rhombic_lattice_of_pos ht ha.1 ha.2)).restrictScalars (𝕜 := ℝ)).comp
      (Complex.ofRealCLM.analyticAt a)
    exact ((analyticAt_const.mul (analyticAt_const.sub zeta)).mul (P a ha)).sub
      ((analyticAt_const.mul ((Complex.ofRealCLM.analyticAt a).sub analyticAt_const)).mul
        (originalComplexWeight_a_analyticAt ht ha))
  have known : deriv (originalSlopingPeriod t) =ᶠ[𝓝 (1/2:ℝ)] D := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)] with a ha
    exact (originalSlopingPeriod_a_hasDerivAt ht ha).deriv
  have extended := P.deriv.eqOn_of_preconnected_of_eventuallyEq rhs isPreconnected_Ioo
    (by norm_num : (1/2:ℝ) ∈ Ioo 0 2) known
  filter_upwards [Ioo_mem_nhds (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<2)] with a ha
  exact extended ha

/-- The original complex period on the descending generator has the stated
second derivative, before taking any real part. -/
theorem originalSigmaPeriod_second_deriv_one {t : ℝ} (ht : 0<t) :
    deriv (deriv (originalSigmaPeriod t)) 1 = -2*slopingIntegral t
      (fun z => ((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP 1)^2) := by
  let L := rhombicPeriodPair t ht
  let z := originalPeriodPath t
  let e := L.weierstrassP 1
  have h1 : (1:ℝ) ∈ Ioo 0 2 := by norm_num
  have reg : (1:ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht h1.1 h1.2
  have hζ := (thetaZeta_hasDerivAt_of_pos ht ht reg).comp_ofReal
  have hP := (originalSlopingPeriod_a_analyticAt ht h1).differentiableAt.hasDerivAt
  have hQ := (originalComplexWeight_a_analyticAt ht h1).differentiableAt.hasDerivAt
  have hd := (((hζ.const_sub (thetaEtaExpression t)).const_mul (2:ℂ)).mul hP).sub
    (((((hasDerivAt_id (1:ℝ)).ofReal_comp).sub_const (1:ℂ)).const_mul 2).mul hQ)
  have derivGerm : deriv (originalSigmaPeriod t) =ᶠ[𝓝 (1:ℝ)] deriv (originalSlopingPeriod t) :=
    (originalSigmaPeriod_eventuallyEq_a ht h1).deriv
  have hd' : HasDerivAt (fun a : ℝ =>
      2*(thetaEtaExpression t-thetaZeta t a)*originalSlopingPeriod t a-
      2*((a:ℂ)-1)*originalComplexWeight t ht a) _ 1 := hd
  rw [derivGerm.deriv_eq,(sloping_deriv_germ_at_one ht).deriv_eq,hd'.deriv]
  simp only [thetaZeta_one,sub_self,mul_zero,zero_mul,add_zero,id_eq,Complex.ofReal_one,
    mul_one,neg_neg]
  have regular {s : ℝ} (hs : s ∈ Icc (-1:ℝ) 1) : z s ∉ L.lattice :=
    rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht hs)
  have cz : Continuous z := continuous_iff_continuousAt.mpr fun s => (originalPeriodPath_hasDerivAt t s).continuousAt
  have cP : ContinuousOn (fun s => L.weierstrassP (z s)) (Icc (-1:ℝ) 1) :=
    fun s hs => ((L.analyticOnNhd_weierstrassP _ (regular hs)).continuousAt.comp cz.continuousAt).continuousWithinAt
  have cA : ContinuousOn (fun s => thetaA t 1 (z s)) (Icc (-1:ℝ) 1) :=
    fun s hs => ((thetaA_analyticAt_off_lattice ht 1 (regular hs)).continuousAt.comp cz.continuousAt).continuousWithinAt
  have iA := cA.intervalIntegrable_of_Icc (by norm_num : (-1:ℝ)≤1) (μ:=volume)
  have iPA : IntervalIntegrable (fun s => L.weierstrassP (z s)*thetaA t 1 (z s)) volume (-1:ℝ) 1 :=
    (cP.mul cA).intervalIntegrable_of_Icc (by norm_num : (-1:ℝ)≤1)
  have moments : (∫ s : ℝ in (-1)..1, (L.weierstrassP (z s)-e)^2) =
      (∫ s : ℝ in (-1)..1, L.weierstrassP (z s)*thetaA t 1 (z s)) -
        e*(∫ s : ℝ in (-1)..1, thetaA t 1 (z s)) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub iPA (iA.const_mul e)]
    apply intervalIntegral.integral_congr
    intro s hs
    have eq := thetaA_one_eq_weierstrassP ht (regular
      (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ)≤1)] using hs))
    change (L.weierstrassP (z s)-e)^2 = L.weierstrassP (z s)*thetaA t 1 (z s)-e*thetaA t 1 (z s)
    rw [eq]
    dsimp [e,L]
    ring
  change 2*e*originalSlopingPeriod t 1-2*originalComplexWeight t ht 1 =
    -2*(((1-I*t)/2)*(∫ s : ℝ in (-1)..1, (L.weierstrassP (z s)-e)^2))
  rw [moments]
  unfold originalSlopingPeriod originalComplexWeight slopingIntegral
  dsimp only [z,L]
  ring

/-- The real part of the second derivative of the actual complex period,
evaluated independently via its equality of germs with the horizontal period. -/
theorem originalSigmaPeriod_second_deriv_one_re {t : ℝ} (ht : 0<t) :
    (deriv (deriv (originalSigmaPeriod t)) 1).re = -2*ellipticI t ht := by
  have h1 : (1:ℝ) ∈ Ioo 0 2 := by norm_num
  have localRe {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 2) :
      thetaHorizontalPeriod t =ᶠ[𝓝 a] fun b => (originalSigmaPeriod t b).re := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact (originalSigmaPeriod_re_eq_horizontal ht hb).symm
  have first : deriv (thetaHorizontalPeriod t) =ᶠ[𝓝 (1:ℝ)] fun b => (deriv (originalSigmaPeriod t) b).re := by
    filter_upwards [isOpen_Ioo.mem_nhds h1] with b hb
    exact ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt b
      (originalSigmaPeriod_a_analyticAt ht hb).differentiableAt.hasDerivAt).congr_of_eventuallyEq
      (localRe hb)).deriv
  have second := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt (1:ℝ)
    (originalSigmaPeriod_a_analyticAt ht h1).deriv.differentiableAt.hasDerivAt).congr_of_eventuallyEq first
  exact second.deriv.symm.trans (horizontal_second_deriv_one ht)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalComplexWeight_a_analyticAt
#print axioms TwoAxisHelicoid.originalSigmaPeriod_second_deriv_one
#print axioms TwoAxisHelicoid.originalSigmaPeriod_second_deriv_one_re
