import TwoAxisHelicoid.LopezRosNullFamily
import TwoAxisHelicoid.WeierstrassRotation
import TwoAxisHelicoid.HolomorphicImmersionCoordinateChange

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

/-- Scaling the coordinate parameter multiplies all three coefficients
by the same complex number, which commutes with López–Ros deformation. -/
theorem lopezRosCoefficients_scale (k d : ℂ) (p : Fin 3 → ℂ) :
    lopezRosCoefficients k (fun j => d*p j) = fun j => d*lopezRosCoefficients k p j := by
  funext j
  fin_cases j <;> simp [lopezRosCoefficients,lopezRosHorizontal] <;> ring

theorem lopezRosCoefficients_weierstrassTriple (k g h : ℂ) :
    lopezRosCoefficients k (weierstrassTriple g h)=weierstrassTriple (k*g) h := by
  funext j
  fin_cases j <;> simp [lopezRosCoefficients,lopezRosHorizontal,lopezRosAverage,lopezRosSkew,weierstrassTriple]
    <;> ring_nf
  all_goals simp [I_sq]
  all_goals ring

theorem nullRealDerivative_injective_coefficients : Function.Injective nullRealDerivative := by
  intro p q h
  funext j
  apply realCoefficientDerivative_injective
  ext w
  exact congrArg (fun F : ℂ →L[ℝ] (Fin 3 → ℝ) => F w j) h

theorem hasFDerivAt_null_comp_holomorphic {X : ℂ → Fin 3 → ℝ} {u : ℂ → ℂ} {z d : ℂ} {p : Fin 3 → ℂ}
    (h : HasFDerivAt X (nullRealDerivative p) (u z)) (hu : HasDerivAt u d z) :
    HasFDerivAt (X ∘ u) (nullRealDerivative (fun j => d*p j)) z := by
  have eq : (nullRealDerivative p).comp ((ContinuousLinearMap.smulRight (1:ℂ →L[ℂ] ℂ) d).restrictScalars ℝ) =
      nullRealDerivative (fun j => d*p j) := by
    ext v j
    change ((v*d)*p j).re=(v*(d*p j)).re
    rw [mul_assoc]
  exact eq ▸ h.comp z (hu.hasFDerivAt.restrictScalars ℝ)

/-- The deformed differential in any holomorphic parameter is obtained
by multiplying that parameter's original Gauss function by k. -/
theorem lopezRos_derivative_in_holomorphic_parameter {X Y U V : ℂ → Fin 3 → ℝ} {u : ℂ → ℂ}
    {z d k g h : ℂ} {p : Fin 3 → ℂ} (hu : HasDerivAt u d z)
    (hx : HasFDerivAt X (nullRealDerivative p) (u z))
    (hy : HasFDerivAt Y (nullRealDerivative (lopezRosCoefficients k p)) (u z))
    (ex : U =ᶠ[𝓝 z] X ∘ u) (ey : V =ᶠ[𝓝 z] Y ∘ u)
    (base : HasFDerivAt U (nullRealDerivative (weierstrassTriple g h)) z) :
    HasFDerivAt V (nullRealDerivative (weierstrassTriple (k*g) h)) z := by
  have hX := (hasFDerivAt_null_comp_holomorphic hx hu).congr_of_eventuallyEq ex
  have hY := (hasFDerivAt_null_comp_holomorphic hy hu).congr_of_eventuallyEq ey
  have coeff := nullRealDerivative_injective_coefficients (hX.unique base)
  rw [← lopezRosCoefficients_weierstrassTriple,← coeff,lopezRosCoefficients_scale]
  exact hY

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lopezRos_derivative_in_holomorphic_parameter
