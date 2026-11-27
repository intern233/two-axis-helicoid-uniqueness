import TwoAxisHelicoid.HolomorphicNullImmersion
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace TwoAxisHelicoid
open Complex

noncomputable def coordinateToEuclidean : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

@[simp] theorem coordinateToEuclidean_apply (v : Fin 3 → ℝ) :
    coordinateToEuclidean v = WithLp.toLp 2 v := rfl

theorem nullRealDerivative_euclidean_norm_sq {p : Fin 3 → ℂ} (hp : ComplexNull p) (v : ℂ) :
    ‖coordinateToEuclidean (nullRealDerivative p v)‖^2 = nullMetric p*‖v‖^2 := by
  have hid := complexNull_real_identities hp
  rw [EuclideanSpace.real_norm_sq_eq,← Complex.normSq_eq_norm_sq]
  simp only [Fin.sum_univ_succ,coordinateToEuclidean_apply,
    nullRealDerivative_apply,Complex.mul_re,Complex.normSq_apply]
  change (v.re*(p 0).re-v.im*(p 0).im)^2+
    ((v.re*(p 1).re-v.im*(p 1).im)^2+((v.re*(p 2).re-v.im*(p 2).im)^2+0)) =
      nullMetric p*(v.re*v.re+v.im*v.im)
  unfold nullMetric at hid ⊢
  linear_combination -v.im^2*hid.1-2*v.re*v.im*hid.2

theorem nullRealDerivative_euclidean_norm {p : Fin 3 → ℂ}
    (hp : ComplexNull p) (hn : p ≠ 0) (v : ℂ) :
    ‖coordinateToEuclidean (nullRealDerivative p v)‖ = Real.sqrt (nullMetric p)*‖v‖ := by
  have hs := nullRealDerivative_euclidean_norm_sq hp v
  have hm := Real.sq_sqrt (nullMetric_pos hp hn).le
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,hm]
  exact hs

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.nullRealDerivative_euclidean_norm
