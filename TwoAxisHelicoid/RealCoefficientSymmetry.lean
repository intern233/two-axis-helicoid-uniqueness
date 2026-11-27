import TwoAxisHelicoid.HarmonicComplexCoefficient
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology ComplexConjugate

theorem realCoefficientDerivative_injective : Function.Injective realCoefficientDerivative := by
  intro a b h
  have h1 := congrArg (fun D : ℂ →L[ℝ] ℝ => D 1) h
  have hI := congrArg (fun D : ℂ →L[ℝ] ℝ => D I) h
  apply Complex.ext
  · simpa [realCoefficientDerivative] using h1
  · simpa [realCoefficientDerivative,Complex.mul_re] using hI

theorem realCoefficientDerivative_conjugation (a : ℂ) :
    (realCoefficientDerivative a).comp Complex.conjCLE.toContinuousLinearMap =
      realCoefficientDerivative (conj a) := by
  ext w
  simp [realCoefficientDerivative,Complex.mul_re]

theorem realCoefficientDerivative_neg_input (a : ℂ) :
    (realCoefficientDerivative a).comp (-ContinuousLinearMap.id ℝ ℂ) =
      realCoefficientDerivative (-a) := by
  ext w
  simp [realCoefficientDerivative,Complex.mul_re]

theorem real_primitive_scalar_mul_derivative {F : ℂ → ℝ} {a z : ℂ}
    (hF : HasFDerivAt F (realCoefficientDerivative a) z) (ε : ℝ) :
    HasFDerivAt (fun w => ε*F w) (realCoefficientDerivative ((ε : ℂ)*a)) z := by
  convert hF.const_mul ε using 1
  ext w
  simp [realCoefficientDerivative,Complex.mul_re,Complex.mul_im]
  ring

theorem real_primitive_translation_coefficient {F : ℂ → ℝ} {a b z ω : ℂ}
    (hF : HasFDerivAt F (realCoefficientDerivative a) z)
    (hshift : HasFDerivAt F (realCoefficientDerivative b) (z+ω))
    (he : (fun w => F (w+ω)) =ᶠ[𝓝 z] F) : b = a := by
  have hd := (hshift.comp z ((hasFDerivAt_id z).add_const ω)).congr_of_eventuallyEq he.symm
  apply realCoefficientDerivative_injective
  simpa using hd.unique hF

theorem real_primitive_negation_coefficient {F : ℂ → ℝ} {a b z : ℂ} (ε : ℝ)
    (hF : HasFDerivAt F (realCoefficientDerivative a) z)
    (hneg : HasFDerivAt F (realCoefficientDerivative b) (-z))
    (he : (fun w => F (-w)) =ᶠ[𝓝 z] (fun w => ε*F w)) : b = -(ε : ℂ)*a := by
  have hd := (hneg.comp z (hasFDerivAt_id z).neg).congr_of_eventuallyEq he.symm
  have heq := hd.unique (real_primitive_scalar_mul_derivative hF ε)
  rw [realCoefficientDerivative_neg_input] at heq
  have h := realCoefficientDerivative_injective heq
  linear_combination -h

theorem real_primitive_conjugation_coefficient {F : ℂ → ℝ} {a b z : ℂ} (ε : ℝ)
    (hF : HasFDerivAt F (realCoefficientDerivative a) z)
    (hconj : HasFDerivAt F (realCoefficientDerivative b) (conj z))
    (he : (fun w => F (conj w)) =ᶠ[𝓝 z] (fun w => ε*F w)) : b = (ε : ℂ)*conj a := by
  have hd := (hconj.comp z Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).congr_of_eventuallyEq he.symm
  have heq := hd.unique (real_primitive_scalar_mul_derivative hF ε)
  rw [realCoefficientDerivative_conjugation] at heq
  have h := congrArg conj (realCoefficientDerivative_injective heq)
  simpa using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.real_primitive_conjugation_coefficient
