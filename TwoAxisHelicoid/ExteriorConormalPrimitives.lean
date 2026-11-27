import TwoAxisHelicoid.ExteriorCirclePrimitive
import TwoAxisHelicoid.SpatialConormalFlux
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace TwoAxisHelicoid
open Complex Set MeasureTheory

/-- The positively oriented boundary circle of an exterior subend. -/
noncomputable def exteriorFluxCircle {R r : ℝ} (hR : 0 < R) (hr : R < r) :
    ComplexPeriodArc {z : ℂ | R < ‖z‖} where
  left := 0
  right := 2*Real.pi
  ordered := Real.two_pi_pos.le
  curve := circleMap 0 r
  velocity θ := circleMap 0 r θ*I
  stays θ _ := by change R < ‖circleMap 0 r θ‖; rwa [norm_circleMap_zero,abs_of_pos (hR.trans hr)]
  continuous_curve := (continuous_circleMap _ _).continuousOn
  continuous_velocity := ((continuous_circleMap _ _).mul continuous_const).continuousOn
  derivative θ _ := hasDerivAt_circleMap 0 r θ

private theorem fluxCircle_angular_integral {R r : ℝ} (hR : 0 < R) (hr : R < r) (f : ℂ → ℂ) :
    (exteriorFluxCircle hR hr).integral f = exteriorAngularPeriod f r := by
  unfold exteriorAngularPeriod ComplexPeriodArc.integral exteriorFluxCircle
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp [circleMap,mul_comm,mul_assoc,mul_left_comm]

/-- For a single-valued immersion the real periods vanish by the
fundamental theorem of calculus. Zero Euclidean conormal flux on just one
circle kills the imaginary periods too. The actual coordinate forms then
have simultaneous single-valued complex primitives on the full annulus. -/
theorem exterior_primitive_of_zero_spatial_flux {R r : ℝ} (hR : 0 < R) (hr : R < r)
    (X : ℂ → Fin 3 → ℝ) (p : ℂ → Fin 3 → ℂ)
    (hd : ∀ z : ℂ, R < ‖z‖ → HasFDerivAt X (nullRealDerivative (p z)) z)
    (hn : ∀ z : ℂ, R < ‖z‖ → ComplexNull (p z))
    (hh : ∀ z : ℂ, R < ‖z‖ → ∀ j, DifferentiableAt ℂ (fun w => p w j) z)
    (flux : ∀ j, (exteriorFluxCircle hR hr).spatialConormalFlux X j = 0) :
    ∃ P : Fin 3 → ℂ → ℂ, ∀ j, ∀ z : ℂ, R < ‖z‖ → HasDerivAt (P j) (p z j) z := by
  let a := exteriorFluxCircle hR hr
  have prim (j : Fin 3) : ∃ F : ℂ → ℂ, ∀ z : ℂ, R < ‖z‖ → HasDerivAt F (p z j) z := by
    apply exterior_primitive_of_zero_angular_period hR hr (fun z hz => hh z hz j)
    have cont : ContinuousOn (fun z => p z j) {z : ℂ | R < ‖z‖} :=
      fun z hz => (hh z hz j).continuousAt.continuousWithinAt
    have dj (z : ℂ) (hz : R < ‖z‖) :
        HasFDerivAt (fun w => X w j) (realCoefficientDerivative (p z j)) z := by
      have h := (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp z (hd z hz)
      convert h using 1
      · rfl
      · ext v
        rfl
    have re := a.integral_re_eq_sub (X := fun z => X z j) cont dj
    have close : a.curve a.right = a.curve a.left := by
      change circleMap 0 r (2*Real.pi) = circleMap 0 r 0
      simpa only [zero_add] using (periodic_circleMap 0 r) 0
    rw [close,sub_self] at re
    rw [← fluxCircle_angular_integral hR hr]
    exact Complex.ext re ((a.spatialConormalFlux_eq_im X p hd hn j cont).symm.trans (flux j))
  choose P h using prim
  exact ⟨P,h⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exterior_primitive_of_zero_spatial_flux
