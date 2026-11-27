import TwoAxisHelicoid.RightSecondOrderRemainder
import TwoAxisHelicoid.RightAnalyticExtension
import TwoAxisHelicoid.EllipticParameterAnalytic
import TwoAxisHelicoid.AnalyticQuadraticRemainder
import Mathlib.Analysis.Asymptotics.Ring

namespace TwoAxisHelicoid
open Filter Asymptotics
open scoped Topology
attribute [local irreducible] actualPeriodAlong ellipticFReal ellipticIReal

/-- The actual variable-coefficient expansion in Appendix A.2. -/
theorem actualPeriodAlong_manuscript_right_expansion :
    (fun t : ℝ => actualPeriodAlong t+ellipticFReal t+
      ellipticIReal t/Real.pi*(ellipticVerticalUpper-t))
      =O[𝓝[<] ellipticVerticalUpper] (fun t => (ellipticVerticalUpper-t)^2) := by
  let T := ellipticVerticalUpper
  have hF0 : ellipticFReal T = Real.pi/T := by
    have hh := thetaG_one_eq_ellipticFReal T
    rw [thetaG_vertical_upper_one_zero,Complex.zero_re] at hh
    linarith
  have hF : (fun t : ℝ => ellipticFReal t-ellipticFReal T-deriv ellipticFReal T*(t-T))
      =O[𝓝[<] T] (fun t => (T-t)^2) := by
    have hh := (analytic_quadratic_remainder (ellipticFReal_analyticAt ellipticVerticalUpper_pos)).mono (l := 𝓝[<] T) nhdsWithin_le_nhds
    exact hh.congr_right (fun t => by ring)
  have hI := ((ellipticIReal_analyticAt ellipticVerticalUpper_pos).differentiableAt.isBigO_sub
    |>.mono (l := 𝓝[<] T) nhdsWithin_le_nhds).mul (isBigO_refl (fun t : ℝ => t-T) (𝓝[<] T))
  have hI' : (fun t : ℝ => (ellipticIReal t-ellipticIReal T)/Real.pi*(T-t))
      =O[𝓝[<] T] (fun t => (T-t)^2) := by
    exact (hI.const_mul_left (-1/Real.pi)).congr (fun t => by ring) (fun t => by ring)
  have hsum := (actualPeriodAlong_right_remainder_isBigO.add hF).add hI'
  apply hsum.congr_left
  intro t
  change (actualPeriodAlong t+Real.pi/T-
      (-deriv ellipticFReal T+ellipticI T ellipticVerticalUpper_pos/Real.pi)*(t-T)+
      (ellipticFReal t-ellipticFReal T-deriv ellipticFReal T*(t-T)))+
      (ellipticIReal t-ellipticIReal T)/Real.pi*(T-t) = _
  rw [hF0,ellipticIReal_eq ellipticVerticalUpper_pos]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_manuscript_right_expansion
