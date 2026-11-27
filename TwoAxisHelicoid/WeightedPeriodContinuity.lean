import TwoAxisHelicoid.RightCoefficientIdentity
import TwoAxisHelicoid.GaussDifferential

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology ComplexConjugate
attribute [local irreducible] thetaJet thetaQuotient thetaLogSecond thetaA thetaZeta

noncomputable def thetaP (t : ℝ) (z : ℂ) : ℂ := thetaLogSecond t z-thetaEtaExpression t

theorem thetaP_eq_weierstrassP {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) : thetaP t z = (rhombicPeriodPair t ht).weierstrassP z := by
  unfold thetaP
  rw [thetaLogSecond_eq_weierstrassP_add_eta_of_pos ht ht hz,add_sub_cancel_right]

theorem thetaEtaExpression_continuousAt {t : ℝ} (ht : 0 < t) : ContinuousAt thetaEtaExpression t := by
  have h1 := (thetaJet_parameter_hasDerivAt ht 1 0).continuousAt
  have h3 := (thetaJet_parameter_hasDerivAt ht 3 0).continuousAt
  have hc : ContinuousAt (fun s => -(Real.pi^2/12:ℂ)*(thetaJet s 3 0/thetaJet s 1 0)) t :=
    continuousAt_const.mul (h3.div h1 (thetaJet_one_at_zero_ne_zero_of_pos ht))
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact thetaEtaExpression_jet_ratio hs

theorem thetaP_real_joint_continuousAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    ContinuousAt (fun p : ℝ × ℝ => (thetaP p.1 p.2).re) (t,a) := by
  have h1 := theta_vertical_quotient_continuousAt ht ha.1 ha.2 1
  have h2 := theta_vertical_quotient_continuousAt ht ha.1 ha.2 2
  have hη : ContinuousAt (fun p : ℝ × ℝ => thetaEtaExpression p.1) (t,a) :=
    (thetaEtaExpression_continuousAt ht).comp (f := fun p : ℝ × ℝ => p.1) (x := (t,a)) continuous_fst.continuousAt
  unfold thetaP thetaLogSecond
  exact Complex.continuous_re.continuousAt.comp ((continuousAt_const.mul ((h1.pow 2).sub h2)).sub hη)

noncomputable def thetaWeightedPeriod (t a : ℝ) : ℂ :=
  (1/2:ℂ)*(∫ x : ℝ in (-1)..1, thetaP t ((x:ℂ)+I*((t/2:ℝ):ℂ))*thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ)))

theorem thetaWeightedPeriod_eq_fullComplexWeight {t : ℝ} (ht : 0 < t) (a : ℝ) :
    thetaWeightedPeriod t a = fullComplexWeight t ht a := by
  unfold thetaWeightedPeriod fullComplexWeight
  simp_rw [thetaP_eq_weierstrassP ht (rhombic_midline_not_mem ht _)]

theorem thetaWeightedPeriod_joint_continuousAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    ContinuousAt (fun p : ℝ × ℝ => thetaWeightedPeriod p.1 p.2) (t,a) := by
  let S := horizontalDomain ×ˢ (univ:Set ℝ)
  let z := fun p : (ℝ × ℝ) × ℝ => (p.2:ℂ)+I*((p.1.1/2:ℝ):ℂ)
  have hu : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => p.1.1) S := by fun_prop
  have hz : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => Real.pi*z p/2) S := by fun_prop
  have hq (j : ℕ) := thetaQuotient_comp_continuousOn hu hz
    (fun p hp => hp.1.1) (fun p hp => horizontal_midline_regular hp.1.1 p.2) j
  have hη : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => thetaEtaExpression p.1.1) S := by
    intro p hp
    exact (thetaEtaExpression_continuousAt hp.1.1).comp_continuousWithinAt
      (f := fun q : (ℝ × ℝ) × ℝ => q.1.1) (hu p hp)
  have hP : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => thetaP p.1.1 (z p)) S := by
    unfold thetaP thetaLogSecond
    exact (continuousOn_const.mul (((hq 1).pow 2).sub (hq 2))).sub hη
  have hA := horizontal_composite_continuousOn (S := S)
    (u := fun p : (ℝ × ℝ) × ℝ => p.1.1) (b := fun p => p.1.2) (x := Prod.snd)
    (by fun_prop) (by fun_prop) (by fun_prop) (fun _ hp => hp.1.1) (fun _ hp => hp.1.2)
  have hprod : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      thetaP p.1.1 (z p)*thetaA p.1.1 p.1.2 (z p)) S := hP.mul hA.1
  have hi := intervalIntegral_parameter_continuousOn horizontalDomain_isOpen
    (f := fun p : ℝ × ℝ => fun x : ℝ => thetaP p.1 ((x:ℂ)+I*((p.1/2:ℝ):ℂ))*
      thetaA p.1 p.2 ((x:ℂ)+I*((p.1/2:ℝ):ℂ))) hprod (-1) 1 (by norm_num)
  have hnh : horizontalDomain ∈ 𝓝 (t,a) := horizontalDomain_isOpen.mem_nhds ⟨ht,ha⟩
  have hc := hi.continuousAt hnh
  unfold thetaWeightedPeriod
  exact continuousAt_const.mul hc

theorem thetaZeta_real (t a : ℝ) : (thetaZeta t a).im = 0 := by
  have h := congrArg Complex.im (thetaZeta_conj t (a:ℂ))
  simp only [Complex.conj_ofReal,Complex.conj_im] at h
  linarith

noncomputable def periodK (t a : ℝ) : ℝ := 2*((thetaEtaExpression t).re-(thetaZeta t a).re)

theorem periodK_one (t : ℝ) : periodK t 1 = 0 := by simp [periodK,thetaZeta_one]

theorem periodK_a_hasDerivAt {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (periodK t) (2*(thetaP t a).re) a := by
  have hz := real_not_mem_rhombic_lattice_of_pos ht ha.1 ha.2
  have hd := (thetaZeta_hasDerivAt_of_pos ht ht hz).comp_ofReal
  have hr := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hd).const_sub (thetaEtaExpression t).re
  have hh := hr.const_mul 2
  convert hh using 1
  · rfl
  · rw [thetaP_eq_weierstrassP ht hz]
    simp

theorem horizontalPeriodDa_elliptic_formula {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    horizontalPeriodDa t a = periodK t a*thetaHorizontalPeriod t a-2*(a-1)*(thetaWeightedPeriod t a).re := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a (fullComplexPeriod_a_hasDerivAt ht ha)
  have he : (fun b : ℝ => (fullComplexPeriod t b).re) = thetaHorizontalPeriod t := funext (fullComplexPeriod_re t)
  change HasDerivAt (fun b : ℝ => (fullComplexPeriod t b).re) _ a at hd
  rw [he] at hd
  have hh := (horizontal_period_a_hasDerivAt ht ha).unique hd
  rw [thetaWeightedPeriod_eq_fullComplexWeight ht]
  simpa [periodK,Complex.mul_re,Complex.mul_im,thetaEtaExpression_real,thetaZeta_real,fullComplexPeriod_re] using hh

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaWeightedPeriod_joint_continuousAt
#print axioms TwoAxisHelicoid.horizontalPeriodDa_elliptic_formula
