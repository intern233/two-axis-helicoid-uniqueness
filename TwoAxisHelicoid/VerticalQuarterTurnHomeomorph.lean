import TwoAxisHelicoid.WeierstrassRotation

namespace TwoAxisHelicoid
open Complex Topology

noncomputable def verticalQuarterTurnHomeomorph : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) where
  toFun := verticalRotation I
  invFun := verticalRotation (-I)
  left_inv v := by ext j; fin_cases j <;> simp [verticalRotation_apply]
  right_inv v := by ext j; fin_cases j <;> simp [verticalRotation_apply]
  continuous_toFun := (verticalRotation I).continuous
  continuous_invFun := (verticalRotation (-I)).continuous

@[simp] theorem verticalQuarterTurnHomeomorph_apply (v : Fin 3 → ℝ) :
    verticalQuarterTurnHomeomorph v = verticalRotation I v := rfl

@[simp] theorem verticalQuarterTurnHomeomorph_symm_apply (v : Fin 3 → ℝ) :
    verticalQuarterTurnHomeomorph.symm v = verticalRotation (-I) v := rfl

theorem vertical_quarter_turn_embedding_iff {M : Type*} [TopologicalSpace M]
    (X : M → Fin 3 → ℝ) :
    IsClosedEmbedding (fun q => verticalRotation I (X q)) ↔ IsClosedEmbedding X := by
  constructor
  · intro h
    have hc := verticalQuarterTurnHomeomorph.symm.isClosedEmbedding.comp h
    have he : (verticalQuarterTurnHomeomorph.symm ∘ fun q => verticalRotation I (X q)) = X := by
      funext q
      exact verticalQuarterTurnHomeomorph.symm_apply_apply (X q)
    rwa [he] at hc
  · intro h
    exact verticalQuarterTurnHomeomorph.isClosedEmbedding.comp h

end TwoAxisHelicoid
