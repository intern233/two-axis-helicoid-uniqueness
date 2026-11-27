import TwoAxisHelicoid.GlobalPeriodUniqueness
import TwoAxisHelicoid.WeierstrassTwoPrimitives

/-! Uniqueness for the actual closed explicit data and their primitives.
This does not assert that every surface in the geometric theorem has already
been represented by these data, or that an embedded global primitive exists. -/
namespace TwoAxisHelicoid
open Complex Set

theorem original_closed_data_parameters_unique {t₁ a₁ c₁ t₂ a₂ c₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (ha₁ : a₁ ∈ Ioo (0 : ℝ) 1) (ha₂ : a₂ ∈ Ioo (0 : ℝ) 1)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hP₁ : ∀ j : Fin 3, (originalCoordinatePeriod t₁ a₁ c₁ ht₁ j).re=0 ∧
      (conjugateCoordinatePeriod t₁ a₁ c₁ ht₁ j).re=0)
    (hP₂ : ∀ j : Fin 3, (originalCoordinatePeriod t₂ a₂ c₂ ht₂ j).re=0 ∧
      (conjugateCoordinatePeriod t₂ a₂ c₂ ht₂ j).re=0) : t₁=t₂ ∧ a₁=a₂ := by
  have h₁ := (original_all_generators_close_iff ht₁ ⟨ha₁.1,by linarith [ha₁.2]⟩ hc₁).mp hP₁
  have h₂ := (original_all_generators_close_iff ht₂ ⟨ha₂.1,by linarith [ha₂.2]⟩ hc₂).mp hP₂
  have he : (t₁,a₁)=(t₂,a₂) := existsUnique_actual_common_period_full_domain.unique
    ⟨ht₁,ha₁,h₁⟩ ⟨ht₂,ha₂,h₂⟩
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

/-- After actual period closure, any two members of the explicit family
have the same parameters and any primitives on a common connected open
coordinate domain are related by a positive Euclidean similarity. -/
theorem original_closed_data_primitives_similar {s : Set ℂ}
    (hs : IsOpen s) (hconn : IsPreconnected s)
    {t₁ a₁ c₁ t₂ a₂ c₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (ha₁ : a₁ ∈ Ioo (0 : ℝ) 1) (ha₂ : a₂ ∈ Ioo (0 : ℝ) 1)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) {q₁ q₂ : ℂ} (hq₁ : ‖q₁‖=1) (hq₂ : ‖q₂‖=1)
    (hP₁ : ∀ j : Fin 3, (originalCoordinatePeriod t₁ a₁ c₁ ht₁ j).re=0 ∧
      (conjugateCoordinatePeriod t₁ a₁ c₁ ht₁ j).re=0)
    (hP₂ : ∀ j : Fin 3, (originalCoordinatePeriod t₂ a₂ c₂ ht₂ j).re=0 ∧
      (conjugateCoordinatePeriod t₂ a₂ c₂ ht₂ j).re=0)
    {X Y : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∈ s, HasFDerivAt X (nullRealDerivative (phasedCoordinateData t₁ a₁ c₁ ht₁ q₁ z)) z)
    (hY : ∀ z ∈ s, HasFDerivAt Y (nullRealDerivative (phasedCoordinateData t₂ a₂ c₂ ht₂ q₂ z)) z) :
    ∃ (scale : ℝ) (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧
        ∀ z ∈ s, WithLp.toLp 2 (Y z)=scale • R (WithLp.toLp 2 (X z))+b := by
  obtain ⟨ht,ha⟩ := original_closed_data_parameters_unique ht₁ ht₂ ha₁ ha₂ hc₁ hc₂ hP₁ hP₂
  subst t₂
  subst a₂
  exact actual_two_coordinate_primitives_similarity hs hconn ht₁ hc₁ hc₂ hq₁ hq₂ hX hY

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_closed_data_primitives_similar
