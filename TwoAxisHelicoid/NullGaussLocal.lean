import TwoAxisHelicoid.NullGaussAlgebra
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology

theorem null_horizontal_minus_analyticAt {p : ℂ → Fin 3 → ℂ} {z : ℂ}
    (hp : ∀ j, AnalyticAt ℂ (fun w => p w j) z) :
    AnalyticAt ℂ (fun w => nullHorizontalMinus (p w)) z :=
  (hp 0).sub (analyticAt_const.mul (hp 1))

theorem null_horizontal_plus_analyticAt {p : ℂ → Fin 3 → ℂ} {z : ℂ}
    (hp : ∀ j, AnalyticAt ℂ (fun w => p w j) z) :
    AnalyticAt ℂ (fun w => nullHorizontalPlus (p w)) z :=
  (hp 0).add (analyticAt_const.mul (hp 1))

theorem null_gauss_simple_zero {p : ℂ → Fin 3 → ℂ} {z : ℂ}
    (hp : ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hm : nullHorizontalMinus (p z) ≠ 0)
    (hzero : p z 2 = 0) (hderiv : deriv (fun w => p w 2) z ≠ 0) :
    AnalyticAt ℂ (fun w => nullGauss (p w)) z ∧ nullGauss (p z) = 0 ∧
      deriv (fun w => nullGauss (p w)) z ≠ 0 := by
  have hminus := null_horizontal_minus_analyticAt hp
  have hd := (hp 2).differentiableAt.hasDerivAt.div hminus.differentiableAt.hasDerivAt hm
  refine ⟨(hp 2).div hminus hm,by simp [nullGauss,hzero],?_⟩
  change deriv ((fun w => p w 2)/(fun w => nullHorizontalMinus (p w))) z ≠ 0
  rw [hd.deriv]
  simp only [hzero,zero_mul,sub_zero]
  exact div_ne_zero (mul_ne_zero hderiv hm) (pow_ne_zero 2 hm)

/-- Regular nullity turns a simple zero of height into a simple meromorphic
pole of the Gauss map when the other horizontal coefficient is nonzero. -/
theorem null_gauss_simple_pole {p : ℂ → Fin 3 → ℂ} {z : ℂ}
    (hp : ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hnull : ∀ᶠ w in 𝓝 z, ComplexNull (p w))
    (hplus : nullHorizontalPlus (p z) ≠ 0)
    (hzero : p z 2 = 0) (hderiv : deriv (fun w => p w 2) z ≠ 0) :
    AnalyticAt ℂ (fun w => (nullGauss (p w))⁻¹) z ∧ (nullGauss (p z))⁻¹ = 0 ∧
      deriv (fun w => (nullGauss (p w))⁻¹) z ≠ 0 := by
  have hplusA := null_horizontal_plus_analyticAt hp
  have he : (fun w => (nullGauss (p w))⁻¹) =ᶠ[𝓝 z]
      (fun w => -p w 2/nullHorizontalPlus (p w)) := by
    filter_upwards [hnull,hplusA.continuousAt.eventually_ne hplus] with w hw hn
    exact null_gauss_inverse_eq hw hn
  have hmodel := (hp 2).neg.div hplusA hplus
  have hd := (((hp 2).differentiableAt.hasDerivAt.neg).div
    hplusA.differentiableAt.hasDerivAt hplus).congr_of_eventuallyEq he
  refine ⟨hmodel.congr he.symm,by simp [nullGauss,hzero],?_⟩
  rw [hd.deriv]
  change ((-deriv (fun w => p w 2) z)*nullHorizontalPlus (p z)-
    (-p z 2)*deriv (fun w => nullHorizontalPlus (p w)) z)/nullHorizontalPlus (p z)^2 ≠ 0
  simp only [hzero,neg_zero,zero_mul,sub_zero]
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hderiv) hplus) (pow_ne_zero 2 hplus)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.null_gauss_simple_zero
#print axioms TwoAxisHelicoid.null_gauss_simple_pole
