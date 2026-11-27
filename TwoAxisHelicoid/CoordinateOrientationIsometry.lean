import TwoAxisHelicoid.NullEuclideanMetric

namespace TwoAxisHelicoid

noncomputable def euclideanOrientationIsometry
    (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ))
    (hR : ∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) :
    EuclideanSpace ℝ (Fin 3) ≃ᵢ EuclideanSpace ℝ (Fin 3) where
  toEquiv := ((WithLp.equiv 2 (Fin 3 → ℝ)).trans R.toEquiv).trans (WithLp.equiv 2 _).symm
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro v w
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp only [dist_eq_norm,EuclideanSpace.real_norm_sq_eq]
    exact hR (WithLp.ofLp v) (WithLp.ofLp w)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.euclideanOrientationIsometry
