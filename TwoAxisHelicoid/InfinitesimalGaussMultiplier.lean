import TwoAxisHelicoid.GaussMultiplierRigidity
import Mathlib.Analysis.Calculus.Deriv.Star

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate

/-- Closure to first order, without assuming closure for any nonzero
parameter value, already kills the real Lopez--Ros amplitude direction. -/
theorem first_order_closed_multiplier_pure_imaginary {c : ℝ → ℂ} {d A : ℂ}
    (hc : HasDerivAt c d 0) (hc0 : c 0 = 1) (hA : A ≠ 0)
    (hclose : HasDerivAt (fun s => (c s)⁻¹*conj A-conj (c s*A)) 0 0) :
    d.re = 0 := by
  have hcn : c 0 ≠ 0 := by rw [hc0]; exact one_ne_zero
  have h₁ := (hc.inv hcn).mul_const (conj A)
  have h₂ : HasDerivAt (fun s => conj (c s*A)) (conj (d*A)) 0 :=
    (hc.mul_const A).star
  have he := (h₁.sub h₂).unique hclose
  simp only [hc0,one_pow,div_one,map_mul] at he
  have he' : (d+conj d)*conj A = 0 := by linear_combination -he
  have hn : conj A ≠ 0 := by simpa using hA
  have hz := (mul_eq_zero.mp he').resolve_right hn
  have hr := congrArg Complex.re hz
  simp only [Complex.add_re,Complex.conj_re,Complex.zero_re] at hr
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.first_order_closed_multiplier_pure_imaginary
