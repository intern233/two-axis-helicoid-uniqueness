import TwoAxisHelicoid.OriginalComplexPeriodDerivative

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology Interval
attribute [local irreducible] thetaSigmaKernel thetaA

noncomputable def originalSigmaWeight (t : ℝ) (ht : 0 < t) (a : ℝ) : ℂ :=
  slopingIntegral t (fun z => (rhombicPeriodPair t ht).weierstrassP z*thetaSigmaKernel t a z)

theorem originalSigmaWeight_eq_theta {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 2) :
    originalSigmaWeight t ht a = originalComplexWeight t ht a := by
  unfold originalSigmaWeight originalComplexWeight slopingIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  change (rhombicPeriodPair t ht).weierstrassP (originalPeriodPath t s)*
      thetaSigmaKernel t a (originalPeriodPath t s) =
    (rhombicPeriodPair t ht).weierstrassP (originalPeriodPath t s)*
      thetaA t a (originalPeriodPath t s)
  rw [thetaSigmaKernel_eq_thetaA_of_pos ht ht (originalPeriodPath t s)
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 ha.2)
    (rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)))]

theorem originalSigmaPeriod_eventuallyEq_a {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 2) :
    originalSigmaPeriod t =ᶠ[𝓝 a] originalSlopingPeriod t := by
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact originalSigmaPeriod_eq_theta ht hb

theorem originalSigmaPeriod_a_analyticAt {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 2) : AnalyticAt ℝ (originalSigmaPeriod t) a :=
  (originalSlopingPeriod_a_analyticAt ht ha).congr
    (originalSigmaPeriod_eventuallyEq_a ht ha).symm

theorem originalSigmaPeriod_t_analyticAt {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 2) :
    AnalyticAt ℝ (fun r : ℝ => originalSigmaPeriod r a) t := by
  apply (originalSlopingPeriod_t_analyticAt ht ha).congr
  filter_upwards [Ioi_mem_nhds ht] with r hr
  exact (originalSigmaPeriod_eq_theta hr ha).symm

theorem originalSigmaPeriod_deriv_at_one {t : ℝ} (ht : 0 < t) :
    deriv (originalSigmaPeriod t) 1 = 0 := by
  rw [(originalSigmaPeriod_eventuallyEq_a ht (by norm_num : (1 : ℝ) ∈ Ioo 0 2)).deriv_eq]
  exact originalSlopingPeriod_deriv_at_one t

theorem originalSigmaPeriod_a_hasDerivAt {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (originalSigmaPeriod t)
      (2*(thetaEtaExpression t-thetaZeta t a)*originalSigmaPeriod t a-
        2*(a-1)*originalSigmaWeight t ht a) a := by
  have ha2 : a ∈ Ioo (0 : ℝ) 2 := ⟨ha.1,by linarith [ha.2]⟩
  rw [originalSigmaPeriod_eq_theta ht ha2,originalSigmaWeight_eq_theta ht ha2]
  exact (originalSlopingPeriod_a_hasDerivAt ht ha).congr_of_eventuallyEq
    (originalSigmaPeriod_eventuallyEq_a ht ha2)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalSigmaPeriod_a_hasDerivAt
#print axioms TwoAxisHelicoid.originalSigmaPeriod_deriv_at_one
