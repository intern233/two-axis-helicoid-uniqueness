import TwoAxisHelicoid.ZetaAxisTranslatedPeriod
import TwoAxisHelicoid.ZetaAxisUniformEndpointError
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TwoAxisHelicoid
open Complex Set Filter MeasureTheory
open scoped Topology Interval
attribute [local irreducible] thetaZeta zetaPoleRegular

/-- On a short segment of length b at either end the pole integrates to
−2i arctan(b/a), on the real arctan branch for a > 0. Both original
integrals are directed upward. -/
theorem zeta_axis_short_segment_integral_errors {t : ℝ} (ht : 0 < t) :
    ∃ δ C : ℝ, 0 < δ ∧ δ < t ∧ 0 ≤ C ∧ ∀ a ∈ Ioo (0 : ℝ) δ, ∀ b ∈ Icc (0 : ℝ) δ,
      let principal := -2*I*(Real.arctan (b/a) : ℂ)
      ‖I*(∫ y : ℝ in 0..b, zetaAxisDifference t a y) - principal‖ ≤ C*a*b ∧
      ‖I*(∫ y : ℝ in 2*t-b..2*t, zetaAxisDifference t a y) - principal‖ ≤ C*a*b := by
  obtain ⟨d,C,dpos,dt,Cpos,estimate⟩ := zeta_axis_uniform_endpoint_errors ht
  let δ := min d 1
  have small : δ ≤ d := min_le_left _ _
  have unit : δ ≤ 1 := min_le_right _ _
  refine ⟨δ,C,lt_min dpos zero_lt_one,small.trans_lt dt,Cpos,?_⟩
  intro a ha b hb principal
  let g := zetaAxisDifference t a
  let P := fun y : ℝ => (-2*I) * ((a/(a^2+y^2) : ℝ) : ℂ)
  have aPos : 0 < a := ha.1
  have admissible : a ∈ Ioo (0 : ℝ) 1 := ⟨aPos,ha.2.trans_le unit⟩
  have realKernel : Continuous (fun y : ℝ => a/(a^2+y^2)) :=
    continuous_const.div (by fun_prop) (fun y => (show 0 < a^2+y^2 by positivity).ne')
  have contP : Continuous P := continuous_const.mul (Complex.continuous_ofReal.comp realKernel)
  have contG : Continuous (fun y => I*g y) := continuous_const.mul (zetaAxisDifference_continuous ht admissible)
  have pValue : (∫ y in 0..b, P y) = principal := by
    dsimp only [P,principal]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal,integral_div_sq_add_sq]
    simp
  have bound : ‖∫ y in 0..b, I*g y-P y‖ ≤ C*a*|b-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [uIoc_of_le hb.1] at hy
    have available := (estimate a ⟨aPos,ha.2.trans_le small⟩ y ⟨hy.1.le,hy.2.trans (hb.2.trans small)⟩).1
    have eq : P y = -2*I*(a : ℂ)/((a : ℂ)^2+(y : ℂ)^2) := by dsimp only [P]; push_cast; ring
    rw [eq]
    exact available
  rw [intervalIntegral.integral_sub (contG.intervalIntegrable _ _) (contP.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,pValue,sub_zero,abs_of_nonneg hb.1] at bound
  have paired (y : ℝ) : g (2*t-y) = g y := by
    dsimp only [g]
    rw [show 2*t-y = -y+2*t by ring,(zetaAxisDifference_periodic ht admissible) (-y),zetaAxisDifference_even]
  have reflected : (∫ y in 0..b, g y) = ∫ y in 2*t-b..2*t, g y := by
    have transport := intervalIntegral.integral_comp_sub_left (a := 0) (b := b) g (2*t)
    simpa only [paired,sub_zero] using transport
  exact ⟨bound,reflected ▸ bound⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.zeta_axis_derivative_wp_integral
#print axioms TwoAxisHelicoid.zeta_axis_uniform_endpoint_errors
#print axioms TwoAxisHelicoid.zeta_axis_short_segment_integral_errors
