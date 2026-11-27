import TwoAxisHelicoid.ThetaSymmetry
import TwoAxisHelicoid.ThetaADerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Holomorphy on the actual denominator domain and cancellation of the moving-path term. -/

namespace TwoAxisHelicoid
set_option maxHeartbeats 800000
open Complex Set MeasureTheory
open scoped Interval

noncomputable def thetaHorizontalPeriod (t a : ℝ) : ℝ :=
  (1/2 : ℝ) * (∫ x : ℝ in (-1)..1, thetaA t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))).re

def thetaRegular (t : ℝ) : Set ℂ := {z | thetaJet t 0 (Real.pi*z/2) ≠ 0}

@[fun_prop] theorem thetaJet_differentiable {t : ℝ} (ht : 0 < t) (j : ℕ) :
    Differentiable ℂ (thetaJet t j) := fun v => (thetaJet_hasDerivAt ht j v).differentiableAt

theorem thetaRegular_isOpen {t : ℝ} (ht : 0 < t) : IsOpen (thetaRegular t) := by
  have hc : Continuous (fun z : ℂ => thetaJet t 0 (Real.pi*z/2)) := by
    exact ((thetaJet_differentiable ht 0).continuous).comp (by fun_prop)
  exact isOpen_ne_fun hc continuous_const

theorem thetaA_differentiableAt {t : ℝ} (ht : 0 < t) (a : ℝ) {z : ℂ}
    (hz : z ∈ thetaRegular t) : DifferentiableAt ℂ (thetaA t a) z := by
  have hd0 := thetaJet_differentiable ht 0
  have hd1 := thetaJet_differentiable ht 1
  change thetaJet t 0 (Real.pi*z/2) ≠ 0 at hz
  unfold thetaA thetaQuotient
  fun_prop (disch := assumption)

theorem thetaA_differentiableOn {t : ℝ} (ht : 0 < t) (a : ℝ) :
    DifferentiableOn ℂ (thetaA t a) (thetaRegular t) :=
  fun _ hz => (thetaA_differentiableAt ht a hz).differentiableWithinAt

theorem thetaA_deriv_continuousOn {t : ℝ} (ht : 0 < t) (a : ℝ) :
    ContinuousOn (deriv (thetaA t a)) (thetaRegular t) :=
  ((thetaA_differentiableOn ht a).deriv (thetaRegular_isOpen ht)).continuousOn

theorem thetaA_horizontal_hasDerivAt {t : ℝ} (ht : 0 < t) (a y x : ℝ)
    (hx : (x : ℂ)+I*y ∈ thetaRegular t) :
    HasDerivAt (fun u : ℝ => thetaA t a ((u : ℂ)+I*y))
      (deriv (thetaA t a) ((x : ℂ)+I*y)) x := by
  have harg := ((hasDerivAt_id x).ofReal_comp).add_const (I*y)
  simpa only [Function.comp_def, id_eq, Complex.ofReal_one, mul_one] using
    (thetaA_differentiableAt ht a hx).hasDerivAt.comp x harg

/-- The entire complex integral of the spatial derivative is zero over one real period. -/
theorem thetaA_integral_spatial_derivative_zero {t : ℝ} (ht : 0 < t) (a y : ℝ)
    (hregular : ∀ x ∈ Set.Icc (-1 : ℝ) 1, (x : ℂ)+I*y ∈ thetaRegular t) :
    (∫ x : ℝ in (-1)..1, deriv (thetaA t a) ((x : ℂ)+I*y)) = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => deriv (thetaA t a) ((x : ℂ)+I*y))
      (Set.Icc (-1 : ℝ) 1) :=
    (thetaA_deriv_continuousOn ht a).comp (by fun_prop) hregular
  have hint : IntervalIntegrable (fun x : ℝ => deriv (thetaA t a) ((x : ℂ)+I*y))
      volume (-1) 1 := hcont.intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (hx : x ∈ Set.uIcc (-1 : ℝ) 1) => thetaA_horizontal_hasDerivAt ht a y x
      (hregular x (by simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx))) hint
  rw [hFTC]
  have hperiod := thetaA_periodic t a ((-1 : ℂ)+I*y)
  have harg : ((-1 : ℂ)+I*y)+2 = (1 : ℂ)+I*y := by ring
  rw [harg] at hperiod
  simpa using sub_eq_zero.mpr hperiod

/-- The path-height term appearing in the parameter derivative of H vanishes. -/
theorem thetaA_moving_height_term_zero {t : ℝ} (ht : 0 < t) (a : ℝ)
    (hregular : ∀ x ∈ Set.Icc (-1 : ℝ) 1, (x : ℂ)+I*((t/2 : ℝ) : ℂ) ∈ thetaRegular t) :
    (1/2 : ℝ) * ((I/2) *
      (∫ x : ℝ in (-1)..1, deriv (thetaA t a) ((x : ℂ)+I*((t/2 : ℝ) : ℂ)))).re = 0 := by
  rw [thetaA_integral_spatial_derivative_zero ht a (t/2) hregular]
  simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_integral_spatial_derivative_zero
