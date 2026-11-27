import TwoAxisHelicoid.PrimitivePeriodNecessity
import TwoAxisHelicoid.WeierstrassTwoPrimitives

namespace TwoAxisHelicoid
open Complex Set

theorem phased_coordinate_primitive_unrotate {t a c : ℝ} (ht : 0 < t)
    {q : ℂ} (hq : ‖q‖ = 1) {X : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      HasFDerivAt X (nullRealDerivative (phasedCoordinateData t a c ht q z)) z) :
    HasTwoAxisHelicoidCoordinateDifferential (fun z => verticalRotation (q⁻¹) (X z)) t a c ht := by
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  intro z hz
  have h := (verticalRotation (q⁻¹)).hasFDerivAt.comp z (hX z hz)
  have he : (verticalRotation (q⁻¹)).comp (nullRealDerivative (phasedCoordinateData t a c ht q z)) =
      nullRealDerivative (coordinateData t a c ht z) := by
    unfold phasedCoordinateData
    rw [nullRealDerivative_complexVerticalRotation]
    ext w j
    change verticalRotation (q⁻¹) (verticalRotation q (nullRealDerivative (coordinateData t a c ht z) w)) j =
      nullRealDerivative (coordinateData t a c ht z) w j
    rw [verticalRotation_mul,inv_mul_cancel₀ hq0,verticalRotation_one]
  rw [he] at h
  exact h

theorem periodic_phased_coordinate_primitive_period_equations {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) {q : ℂ} (hq : ‖q‖ = 1)
    {X : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      HasFDerivAt X (nullRealDerivative (phasedCoordinateData t a c ht q z)) z)
    (hp : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      ∀ ω ∈ (rhombicPeriodPair t ht).lattice, X (z+ω) = X z) :
    thetaG t a = 0 ∧ thetaHorizontalPeriod t a = 0 := by
  apply periodic_actual_primitive_period_equations ht ha hc
    (phased_coordinate_primitive_unrotate ht hq hX)
  intro z hz ω hω
  rw [hp z hz ω hω]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodic_phased_coordinate_primitive_period_equations
