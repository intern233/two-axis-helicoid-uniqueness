import TwoAxisHelicoid.SlopingIntegralBridge
import TwoAxisHelicoid.OriginalPeriodBridge
import TwoAxisHelicoid.MovingEllipticPeriod
import TwoAxisHelicoid.ThetaKernelRegular

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate
attribute [local irreducible] thetaA

theorem rhombic_derivWeierstrassP_conj {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (rhombicPeriodPair t ht).derivWeierstrassP (conj z) =
      conj ((rhombicPeriodPair t ht).derivWeierstrassP z) := by
  unfold PeriodPair.derivWeierstrassP
  rw [map_neg,Complex.conj_tsum]
  congr 1
  rw [← (rhombicConjEquiv t ht).tsum_eq]
  apply tsum_congr
  intro l
  simp only [rhombicConjEquiv,map_sub,map_div₀,map_ofNat,map_pow]
  rfl

theorem elliptic_weight_sloping_re {t : ℝ} (ht : 0 < t) (a : ℝ) (w : ℂ → ℂ)
    (hw : ∀ z ∉ (rhombicPeriodPair t ht).lattice, AnalyticAt ℂ w z)
    (hwc : ∀ z, w (conj z) = conj (w z))
    (hwp : ∀ z, w (z+(1+I*t)) = w z) :
    (slopingIntegral t (fun z => w z*thetaA t a z)).re =
      ((1/2:ℂ)*∫ x : ℝ in (-1)..1,
        w ((x:ℂ)+I*((t/2:ℝ):ℂ))*thetaA t a ((x:ℂ)+I*((t/2:ℝ):ℂ))).re := by
  apply slopingIntegral_re_eq_half_horizontal ht
  · intro z hz
    have hn := rhombic_open_rectangle_not_mem ht hz
    exact ((hw z hn).mul (thetaA_analyticAt_off_lattice ht a hn)).differentiableAt.differentiableWithinAt
  · intro z
    rw [hwc,thetaA_conj,map_mul]
  · intro z
    rw [hwp,thetaA_complex_period ht a]
  · apply continuous_iff_continuousAt.mpr
    intro x
    have hn := rhombic_midline_not_mem ht x
    exact (((hw _ hn).mul (thetaA_analyticAt_off_lattice ht a hn)).continuousAt).comp
      (f := fun x : ℝ => (x:ℂ)+I*((t/2:ℝ):ℂ)) (by fun_prop)

noncomputable def originalWeightedQ (t : ℝ) (ht : 0 < t) (a : ℝ) : ℝ :=
  (slopingIntegral t (fun z => (rhombicPeriodPair t ht).weierstrassP z*thetaA t a z)).re

noncomputable def originalWeightedR (t : ℝ) (ht : 0 < t) (a : ℝ) : ℝ :=
  (slopingIntegral t (fun z => (rhombicPeriodPair t ht).derivWeierstrassP z*thetaA t a z)).re

theorem originalWeightedQ_eq {t : ℝ} (ht : 0 < t) (a : ℝ) :
    originalWeightedQ t ht a = (fullComplexWeight t ht a).re := by
  apply elliptic_weight_sloping_re ht a
  · exact fun z hz => (rhombicPeriodPair t ht).analyticOnNhd_weierstrassP z hz
  · exact rhombic_weierstrassP_conj ht
  · intro z
    exact (rhombicPeriodPair t ht).weierstrassP_add_coe z
      ⟨1+I*t,(rhombicPeriodPair t ht).ω₂_mem_lattice⟩

theorem originalWeightedR_eq {t : ℝ} (ht : 0 < t) (a : ℝ) :
    originalWeightedR t ht a = (fullComplexSlopeWeight t ht a).re := by
  apply elliptic_weight_sloping_re ht a
  · exact fun z hz => (rhombicPeriodPair t ht).analyticOnNhd_derivWeierstrassP z hz
  · exact rhombic_derivWeierstrassP_conj ht
  · intro z
    exact (rhombicPeriodPair t ht).derivWeierstrassP_add_coe z
      ⟨1+I*t,(rhombicPeriodPair t ht).ω₂_mem_lattice⟩

theorem originalPeriodAlong_moving_elliptic_identity {t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    Real.pi*deriv originalPeriodAlong t =
      (2*((rhombicPeriodPair t ht.1).weierstrassP (verticalA t)).re-(thetaEtaExpression t).re+
        2*periodD t (verticalA t)*(thetaW t (verticalA t)).re+
        2*periodD t (verticalA t)*(verticalA t-1)*(thetaEtaExpression t).re)*originalPeriodAlong t+
      (3+2*periodD t (verticalA t)*(verticalA t-1))*originalWeightedQ t ht.1 (verticalA t)-
      (verticalA t-1)*originalWeightedR t ht.1 (verticalA t) := by
  rw [(originalPeriodAlong_eventuallyEq_actual ht).deriv_eq,originalPeriodAlong_eq_actual ht,
    originalWeightedQ_eq,originalWeightedR_eq]
  exact actualPeriodAlong_moving_elliptic_identity ht

theorem originalPeriodAlong_zero_derivative_elliptic {t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) (hz : originalPeriodAlong t = 0) :
    Real.pi*deriv originalPeriodAlong t =
      (3+2*periodD t (verticalA t)*(verticalA t-1))*originalWeightedQ t ht.1 (verticalA t)-
      (verticalA t-1)*originalWeightedR t ht.1 (verticalA t) := by
  rw [originalPeriodAlong_moving_elliptic_identity ht,hz,mul_zero,zero_add]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalPeriodAlong_moving_elliptic_identity
