import TwoAxisHelicoid.OriginalMovingComplexPeriod

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval
attribute [local irreducible] thetaSigmaKernel thetaA originalComplexPeriodAlong

noncomputable def originalSigmaSlopeWeight (t : ℝ) (ht : 0 < t) (a : ℝ) : ℂ :=
  slopingIntegral t (fun z => (rhombicPeriodPair t ht).derivWeierstrassP z*
    thetaSigmaKernel t a z)

theorem originalSigmaSlopeWeight_eq_theta {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 2) :
    originalSigmaSlopeWeight t ht a = originalComplexSlopeWeight t ht a := by
  unfold originalSigmaSlopeWeight originalComplexSlopeWeight slopingIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  change (rhombicPeriodPair t ht).derivWeierstrassP (originalPeriodPath t s)*
      thetaSigmaKernel t a (originalPeriodPath t s) =
    (rhombicPeriodPair t ht).derivWeierstrassP (originalPeriodPath t s)*
      thetaA t a (originalPeriodPath t s)
  rw [thetaSigmaKernel_eq_thetaA_of_pos ht ht (originalPeriodPath t s)
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 ha.2)
    (rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)))]

theorem originalSigmaPeriod_t_hasDerivAt_elliptic {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => originalSigmaPeriod r a)
      (((3-2*(a-1)*thetaW t a)*originalSigmaWeight t ht a-
        (a-1)*originalSigmaSlopeWeight t ht a+
        (2*(rhombicPeriodPair t ht).weierstrassP a-thetaEtaExpression t-
          2*(thetaW t a)^2-2*thetaEtaExpression t*(a-1)*thetaW t a)*
            originalSigmaPeriod t a)/(Real.pi : ℂ)) t := by
  have ha2 : a ∈ Ioo (0 : ℝ) 2 := ⟨ha.1,by linarith [ha.2]⟩
  rw [originalSigmaPeriod_eq_theta ht ha2,originalSigmaWeight_eq_theta ht ha2,
    originalSigmaSlopeWeight_eq_theta ht ha2]
  apply (originalSlopingPeriod_t_hasDerivAt_elliptic ht ha).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with r hr
  exact originalSigmaPeriod_eq_theta hr ha2

noncomputable def originalSigmaComplexPeriodAlong (t : ℝ) : ℂ :=
  originalSigmaPeriod t (verticalA t)

theorem originalSigmaComplexPeriodAlong_eq_theta {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    originalSigmaComplexPeriodAlong t = originalComplexPeriodAlong t := by
  unfold originalSigmaComplexPeriodAlong originalComplexPeriodAlong
  exact originalSigmaPeriod_eq_theta ht.1
    ⟨(verticalA_spec ht).1.1,by linarith [(verticalA_spec ht).1.2]⟩

theorem originalSigmaComplexPeriodAlong_eventuallyEq_theta {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    originalSigmaComplexPeriodAlong =ᶠ[𝓝 t] originalComplexPeriodAlong := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
  exact originalSigmaComplexPeriodAlong_eq_theta hr

theorem originalSigmaComplexPeriodAlong_analyticAt {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    AnalyticAt ℝ originalSigmaComplexPeriodAlong t :=
  (originalComplexPeriodAlong_analyticAt ht).congr
    (originalSigmaComplexPeriodAlong_eventuallyEq_theta ht).symm

theorem originalSigmaComplexPeriodAlong_moving_elliptic_identity {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    (Real.pi : ℂ)*deriv originalSigmaComplexPeriodAlong t =
      (2*(rhombicPeriodPair t ht.1).weierstrassP (verticalA t)-thetaEtaExpression t+
        2*(periodD t (verticalA t) : ℂ)*thetaW t (verticalA t)+
        2*(periodD t (verticalA t) : ℂ)*(verticalA t-1)*thetaEtaExpression t)*
          originalSigmaComplexPeriodAlong t+
      (3+2*(periodD t (verticalA t) : ℂ)*(verticalA t-1))*
        originalSigmaWeight t ht.1 (verticalA t)-
      (verticalA t-1)*originalSigmaSlopeWeight t ht.1 (verticalA t) := by
  have ha : verticalA t ∈ Ioo (0 : ℝ) 2 :=
    ⟨(verticalA_spec ht).1.1,by linarith [(verticalA_spec ht).1.2]⟩
  rw [(originalSigmaComplexPeriodAlong_eventuallyEq_theta ht).deriv_eq,
    originalSigmaComplexPeriodAlong_eq_theta ht,
    originalSigmaWeight_eq_theta ht.1 ha,originalSigmaSlopeWeight_eq_theta ht.1 ha]
  exact originalComplexPeriodAlong_moving_elliptic_identity ht

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalSigmaPeriod_t_hasDerivAt_elliptic
#print axioms TwoAxisHelicoid.originalSigmaComplexPeriodAlong_moving_elliptic_identity
