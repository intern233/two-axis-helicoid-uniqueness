module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace TwoAxisHelicoid
open Filter
open scoped Topology

/-- An odd analytic function normalized by its first and third jets has
a fifth-order remainder. Its logarithmic derivative has a simple pole of
residue one and a third-order analytic remainder. -/
theorem odd_logarithmic_derivative_origin_factors {f g : ℂ → ℂ}
    (analytic : AnalyticAt ℂ f 0) (odd : ∀ z, f (-z) = -f z)
    (tangent : deriv f 0 = 1) (third : iteratedDeriv 3 f 0 = 0)
    (logarithmic : ∀ z, f z ≠ 0 → deriv f z = g z * f z) :
    ∃ A B : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧
      (∀ᶠ z in 𝓝 0, f z = z + z^5 * A z) ∧
      (∀ᶠ z in 𝓝[≠] 0, g z = z⁻¹ + z^3 * B z) := by
  have even_zero (n : ℕ) : iteratedDeriv (2*n) f 0 = 0 := by
    have sign := iteratedDeriv_comp_neg (2*n) f 0
    rw [show (fun z => f (-z)) = fun z => -f z from funext odd, iteratedDeriv_fun_neg] at sign
    simp only [neg_zero, pow_mul, neg_one_sq, one_pow, one_smul] at sign
    linear_combination -sign / 2
  have initial : f 0 = 0 := by simpa using even_zero 0
  have second : iteratedDeriv 2 f 0 = 0 := even_zero 1
  have fourth : iteratedDeriv 4 f 0 = 0 := even_zero 2
  obtain ⟨A, ha, expand⟩ := analytic.exists_eventuallyEq_sum_add_pow_mul 5
  have germ : f =ᶠ[𝓝 0] fun z => z + z^5 * A z := by
    filter_upwards [expand] with z hz
    simpa [Finset.sum_range_succ, smul_eq_mul, initial, iteratedDeriv_one,
      tangent, second, third, fourth] using hz
  let D := fun z : ℂ => 1 + z^4 * A z
  let B := fun z : ℂ => (4 * A z + z * deriv A z) / D z
  have hd : AnalyticAt ℂ D 0 := analyticAt_const.add ((analyticAt_id.pow 4).mul ha)
  have h0 : D 0 ≠ 0 := by simp [D]
  have hb : AnalyticAt ℂ B 0 :=
    ((analyticAt_const.mul ha).add (analyticAt_id.mul ha.deriv)).div hd h0
  refine ⟨A, B, ha, hb, germ, ?_⟩
  have denominator := hd.continuousAt.eventually_ne h0
  filter_upwards [germ.filter_mono nhdsWithin_le_nhds, germ.deriv.filter_mono nhdsWithin_le_nhds,
    ha.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    denominator.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z value derivative localA dz punctured
  have nz : z ≠ 0 := punctured
  have factor : f z = z * D z := by rw [value]; dsimp [D]; ring
  have jet : HasDerivAt (fun w : ℂ => w + w^5 * A w)
      (1 + (5*z^4*A z + z^5*deriv A z)) z := by
    simpa using! (hasDerivAt_id z).fun_add
      ((hasDerivAt_pow 5 z).fun_mul localA.differentiableAt.hasDerivAt)
  have relation := logarithmic z (factor ▸ mul_ne_zero nz dz)
  rw [factor, derivative, jet.deriv] at relation
  apply mul_right_cancel₀ (mul_ne_zero nz dz)
  calc
    g z * (z * D z) = 1 + (5*z^4*A z + z^5*deriv A z) := relation.symm
    _ = (z⁻¹ + z^3 * B z) * (z * D z) := by
      dsimp only [B]
      field_simp [nz, dz]
      dsimp [D]
      ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.odd_logarithmic_derivative_origin_factors
