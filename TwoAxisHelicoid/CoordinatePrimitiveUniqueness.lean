import TwoAxisHelicoid.ActualLocalImmersion
import Mathlib.Analysis.Calculus.MeanValue

namespace TwoAxisHelicoid
open Complex Set

/-- This specifies a global primitive of the actual coordinate forms. Existence
and descent to the punctured torus remain separate period obligations. -/
def HasTwoAxisHelicoidCoordinateDifferential (X : ℂ → Fin 3 → ℝ)
    (t a c : ℝ) (ht : 0 < t) : Prop :=
  ∀ z ∉ (rhombicPeriodPair t ht).lattice,
    HasFDerivAt X (nullRealDerivative (coordinateData t a c ht z)) z

theorem coordinateData_scale (t a c r : ℝ) (ht : 0 < t) (z : ℂ) :
    coordinateData t a (r*c) ht z = r • coordinateData t a c ht z := by
  ext j
  fin_cases j <;> dsimp [coordinateData] <;> push_cast <;> ring

theorem nullRealDerivative_smul (r : ℝ) (p : Fin 3 → ℂ) :
    nullRealDerivative (r • p) = r • nullRealDerivative p := by
  ext w j
  change (w*((r : ℂ)*p j)).re = r*(w*p j).re
  rw [show w*((r : ℂ)*p j) = (r : ℂ)*(w*p j) by ring]
  simp

theorem rhombic_punctured_plane_isConnected {t : ℝ} (ht : 0 < t) :
    IsConnected ((rhombicPeriodPair t ht).lattice : Set ℂ)ᶜ := by
  apply Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
  exact countable_of_Lindelof_of_discrete (X := (rhombicPeriodPair t ht).lattice)

theorem actual_coordinate_primitives_unique_up_to_scale_translation
    {X Y : ℂ → Fin 3 → ℝ} {t a c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : c₁ ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c₁ ht)
    (hY : HasTwoAxisHelicoidCoordinateDifferential Y t a c₂ ht) :
    ∃ b : Fin 3 → ℝ, ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      Y z = (c₂/c₁) • X z+b := by
  let r := c₂/c₁
  have he : r*c₁ = c₂ := div_mul_cancel₀ _ hc₁
  have hscale (z : ℂ) (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
      HasFDerivAt (fun w => r • X w)
        (nullRealDerivative (coordinateData t a c₂ ht z)) z := by
    have h := (hX z hz).const_smul r
    rw [← nullRealDerivative_smul,← coordinateData_scale,he] at h
    exact h
  have hopen := (rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl
  exact hopen.exists_eq_add_of_fderiv_eq (rhombic_punctured_plane_isConnected ht).2
    (fun z hz => (hY z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hscale z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hY z hz).fderiv,(hscale z hz).fderiv])

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_coordinate_primitives_unique_up_to_scale_translation
