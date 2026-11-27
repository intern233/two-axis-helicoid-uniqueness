import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Real MeasureTheory

noncomputable def helicoidGroundState (t : ℝ) : ℝ := (Real.cosh t)⁻¹

theorem helicoidGroundState_hasDerivAt (t : ℝ) :
    HasDerivAt helicoidGroundState (-Real.sinh t/(Real.cosh t)^2) t := by
  exact (Real.hasDerivAt_cosh t).inv (Real.cosh_pos t).ne'

theorem helicoidGroundState_deriv : deriv helicoidGroundState =
    fun t => -Real.sinh t/(Real.cosh t)^2 :=
  funext (fun t => (helicoidGroundState_hasDerivAt t).deriv)

theorem helicoidGroundState_deriv_hasDerivAt (t : ℝ) :
    HasDerivAt (deriv helicoidGroundState)
      (helicoidGroundState t-2*helicoidGroundState t^3) t := by
  rw [helicoidGroundState_deriv]
  convert ((Real.hasDerivAt_sinh t).neg.div ((Real.hasDerivAt_cosh t).pow 2)
    (pow_ne_zero 2 (Real.cosh_pos t).ne')) using 1
  dsimp [helicoidGroundState]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

/-- The exact one-dimensional Jacobi ground-state equation in Appendix D.3. -/
theorem helicoidGroundState_jacobi (t : ℝ) :
    -deriv (deriv helicoidGroundState) t-
      2*helicoidGroundState t^2*helicoidGroundState t = -helicoidGroundState t := by
  rw [(helicoidGroundState_deriv_hasDerivAt t).deriv]
  ring

theorem real_tanh_hasDerivAt (t : ℝ) :
    HasDerivAt Real.tanh (1/(Real.cosh t)^2) t := by
  convert (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne' using 1
  · ext x; exact Real.tanh_eq_sinh_div_cosh x
  · field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq t]

noncomputable def helicoidGroundEnergyDensity (t : ℝ) : ℝ :=
  (deriv helicoidGroundState t)^2-2*helicoidGroundState t^4

theorem helicoidGroundEnergy_primitive (t : ℝ) :
    HasDerivAt (fun x => Real.tanh x^3-2*Real.tanh x)
      (helicoidGroundEnergyDensity t) t := by
  convert ((real_tanh_hasDerivAt t).pow 3).sub ((real_tanh_hasDerivAt t).const_mul 2) using 1
  dsimp [helicoidGroundEnergyDensity,helicoidGroundState]
  rw [helicoidGroundState_deriv,Real.tanh_eq_sinh_div_cosh]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem helicoidGroundEnergyDensity_continuous : Continuous helicoidGroundEnergyDensity := by
  unfold helicoidGroundEnergyDensity
  rw [helicoidGroundState_deriv]
  unfold helicoidGroundState
  fun_prop (disch := intros; positivity)

theorem helicoidGroundEnergy_interval (R : ℝ) :
    (∫ t in (-R)..R, helicoidGroundEnergyDensity t) = 2*(Real.tanh R^3-2*Real.tanh R) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => helicoidGroundEnergy_primitive t)
    (helicoidGroundEnergyDensity_continuous.intervalIntegrable (-R) R)]
  rw [Real.tanh_neg]
  ring

theorem helicoidGroundEnergy_interval_negative {R : ℝ} (hR : 0 < R) :
    (∫ t in (-R)..R, helicoidGroundEnergyDensity t) < 0 := by
  rw [helicoidGroundEnergy_interval]
  have hpos : 0 < Real.tanh R := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hR) (Real.cosh_pos R)
  have hlt := Real.tanh_lt_one R
  nlinarith [sq_nonneg (Real.tanh R),mul_pos hpos (show 0 < 2-Real.tanh R^2 by nlinarith)]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidGroundState_jacobi
#print axioms TwoAxisHelicoid.helicoidGroundEnergy_interval_negative
