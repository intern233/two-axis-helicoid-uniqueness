import TwoAxisHelicoid.HarmonicNullLift

namespace TwoAxisHelicoid
open Complex Set

noncomputable def coordinateSignMap (s : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun j => s j • ContinuousLinearMap.proj j)

@[simp] theorem coordinateSignMap_apply (s v : Fin 3 → ℝ) (j : Fin 3) :
    coordinateSignMap s v j = s j*v j := rfl

theorem coordinateSignMap_involutive {s : Fin 3 → ℝ} (hs : ∀ j, (s j)^2 = 1) :
    Function.Involutive (coordinateSignMap s) := by
  intro v
  ext j
  change s j*(s j*v j) = v j
  rw [← mul_assoc,← pow_two,hs j,one_mul]

noncomputable def coordinateSignHomeomorph {s : Fin 3 → ℝ} (hs : ∀ j, (s j)^2 = 1) :
    (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) where
  toFun := coordinateSignMap s
  invFun := coordinateSignMap s
  left_inv := coordinateSignMap_involutive hs
  right_inv := coordinateSignMap_involutive hs
  continuous_toFun := (coordinateSignMap s).continuous
  continuous_invFun := (coordinateSignMap s).continuous

theorem coordinateSignMap_squared_displacement {s : Fin 3 → ℝ} (hs : ∀ j, (s j)^2 = 1)
    (v w : Fin 3 → ℝ) :
    (∑ j, (coordinateSignMap s v j-coordinateSignMap s w j)^2) = ∑ j, (v j-w j)^2 := by
  apply Finset.sum_congr rfl
  intro j _hj
  rw [coordinateSignMap_apply,coordinateSignMap_apply,← mul_sub,mul_pow,hs j,one_mul]

theorem scalarComplexCoefficient_const_mul {F : ℂ → ℝ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) (s : ℝ) :
    scalarComplexCoefficient (fun w => s*F w) z = (s : ℂ)*scalarComplexCoefficient F z := by
  apply realCoefficientDerivative_injective
  exact (scalarComplexCoefficient_hasFDerivAt (hF.const_mul s)).unique
    (real_primitive_scalar_mul_derivative (scalarComplexCoefficient_hasFDerivAt hF) s)

theorem coordinateSignMap_punctured_coefficient {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) (s : Fin 3 → ℝ) {z : ℂ} (hz : z ∉ L.lattice) :
    puncturedImmersionCoefficient L (fun w => coordinateSignMap s (X w)) z =
      fun j => (s j : ℂ)*puncturedImmersionCoefficient L X z j := by
  rw [puncturedImmersionCoefficient_eq hz,puncturedImmersionCoefficient_eq hz]
  ext j
  exact scalarComplexCoefficient_const_mul ((hX.harmonic z hz j).1.differentiableAt two_ne_zero) (s j)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coordinateSignMap_squared_displacement
#print axioms TwoAxisHelicoid.coordinateSignMap_punctured_coefficient
