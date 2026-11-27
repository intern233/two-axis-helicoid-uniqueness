import TwoAxisHelicoid.OriginalComplexPeriodAlong
import TwoAxisHelicoid.MovingEllipticPeriod
import TwoAxisHelicoid.OriginalSigmaPeriodDerivative

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] originalComplexPeriodAlong originalSlopingPeriod
  originalComplexWeight originalComplexSlopeWeight verticalA thetaW periodD

theorem originalComplexPeriodAlong_moving_elliptic_identity {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    (Real.pi : ℂ)*deriv originalComplexPeriodAlong t =
      (2*(rhombicPeriodPair t ht.1).weierstrassP (verticalA t)-thetaEtaExpression t+
        2*(periodD t (verticalA t) : ℂ)*thetaW t (verticalA t)+
        2*(periodD t (verticalA t) : ℂ)*(verticalA t-1)*thetaEtaExpression t)*
          originalComplexPeriodAlong t+
      (3+2*(periodD t (verticalA t) : ℂ)*(verticalA t-1))*
        originalComplexWeight t ht.1 (verticalA t)-
      (verticalA t-1)*originalComplexSlopeWeight t ht.1 (verticalA t) := by
  have ha := (verticalA_spec ht).1
  have hW : ((thetaW t (verticalA t)).re : ℂ) = thetaW t (verticalA t) := by
    apply Complex.ext <;> simp only [Complex.ofReal_re,Complex.ofReal_im,thetaW_real]
  have hap : ((deriv verticalA t : ℝ) : ℂ) =
      -(thetaW t (verticalA t)+(periodD t (verticalA t) : ℂ))/(Real.pi : ℂ) := by
    rw [verticalA_deriv_WD ht]
    push_cast
    rw [hW]
  have hd := originalSlopingPeriod_t_elliptic_intermediate ht.1 ha
  have hda := (originalSlopingPeriod_a_hasDerivAt ht.1 ha).deriv
  have hk : 2*(thetaEtaExpression t-thetaZeta t (verticalA t)) =
      -2*(thetaW t (verticalA t)+(verticalA t-1)*thetaEtaExpression t) := by
    unfold thetaW
    ring
  rw [hk] at hda
  rw [(originalComplexPeriodAlong_hasDerivAt ht).deriv,hap,hd.deriv]
  rw [hda]
  unfold originalComplexPeriodAlong
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

theorem originalComplexPeriodAlong_zero_derivative_elliptic {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper)
    (hz : originalComplexPeriodAlong t = 0) :
    (Real.pi : ℂ)*deriv originalComplexPeriodAlong t =
      (3+2*(periodD t (verticalA t) : ℂ)*(verticalA t-1))*
        originalComplexWeight t ht.1 (verticalA t)-
      (verticalA t-1)*originalComplexSlopeWeight t ht.1 (verticalA t) := by
  rw [originalComplexPeriodAlong_moving_elliptic_identity ht,hz,mul_zero,zero_add]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalComplexPeriodAlong_moving_elliptic_identity
