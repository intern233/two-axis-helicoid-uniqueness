import TwoAxisHelicoid.ActualPrimitiveThinEnd
import TwoAxisHelicoid.VerticalQuarterTurnHomeomorph
import Mathlib.Topology.Algebra.ConstMulAction

namespace TwoAxisHelicoid
open Complex

noncomputable def axisSpatialNormalization {α : ℝ} (hα : α ≠ 0) (b : Fin 3 → ℝ) :
    (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ) :=
  (((verticalQuarterTurnHomeomorph.trans (Homeomorph.addRight (-verticalRotation I b))).trans
    (Homeomorph.smulOfNeZero α hα)).trans verticalQuarterTurnHomeomorph)

theorem axisSpatialNormalization_apply {α : ℝ} (hα : α ≠ 0) (b v : Fin 3 → ℝ) :
    axisSpatialNormalization hα b v =
      verticalRotation I (α • (verticalRotation I v-verticalRotation I b)) := by
  simp only [axisSpatialNormalization,Homeomorph.trans_apply,verticalQuarterTurnHomeomorph_apply,
    sub_eq_add_neg]
  rfl

theorem axisNormalizedPrimitive_eq_space_map {α : ℝ} (hα : α ≠ 0)
    (X : ℂ → Fin 3 → ℝ) :
    axisNormalizedPrimitive α X = axisSpatialNormalization hα (X 1) ∘ X := by
  funext z
  exact (axisSpatialNormalization_apply hα (X 1) (X z)).symm

/-- The normalization used in the thin-end theorem is a genuine Euclidean
similarity: it scales every squared Euclidean displacement by α². -/
theorem axisSpatialNormalization_squared_displacement {α : ℝ} (hα : α ≠ 0)
    (b u v : Fin 3 → ℝ) :
    (∑ j, (axisSpatialNormalization hα b u j-axisSpatialNormalization hα b v j)^2) =
      α^2*(∑ j, (u j-v j)^2) := by
  have hd : axisSpatialNormalization hα b u-axisSpatialNormalization hα b v =
      verticalRotation I (α • verticalRotation I (u-v)) := by
    rw [axisSpatialNormalization_apply,axisSpatialNormalization_apply,← map_sub,← smul_sub]
    congr 2
    rw [map_sub]
    abel
  change (∑ j, ((axisSpatialNormalization hα b u-axisSpatialNormalization hα b v) j)^2) = _
  rw [hd,verticalRotation_preserves_squared_length (by norm_num : ‖(I : ℂ)‖ = 1)]
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  rw [verticalRotation_preserves_squared_length (by norm_num : ‖(I : ℂ)‖ = 1)]
  rfl

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.axisSpatialNormalization_squared_displacement
