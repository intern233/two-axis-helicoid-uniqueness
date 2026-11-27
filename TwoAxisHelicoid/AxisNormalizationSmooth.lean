import TwoAxisHelicoid.AxisSpatialNormalization
import TwoAxisHelicoid.ImmersionAmbientDiffeomorph

namespace TwoAxisHelicoid
open Complex
open scoped ContDiff

theorem axisSpatialNormalization_contDiff {α : ℝ} (hα : α ≠ 0) (b : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (axisSpatialNormalization hα b) := by
  have he : (axisSpatialNormalization hα b : (Fin 3 → ℝ) → Fin 3 → ℝ) =
      fun v => verticalRotation I (α • (verticalRotation I v-verticalRotation I b)) :=
    funext (axisSpatialNormalization_apply hα b)
  rw [he]
  fun_prop

theorem axisSpatialNormalization_symm_apply {α : ℝ} (hα : α ≠ 0)
    (b v : Fin 3 → ℝ) :
    (axisSpatialNormalization hα b).symm v = b+α⁻¹ • verticalRotation I (verticalRotation I v) := by
  apply (axisSpatialNormalization hα b).injective
  rw [Homeomorph.apply_symm_apply,axisSpatialNormalization_apply]
  ext j
  fin_cases j <;> simp [verticalRotation_apply,Matrix.vecHead,Matrix.vecTail,smul_eq_mul]
    <;> field_simp [hα]

theorem axisSpatialNormalization_symm_contDiff {α : ℝ} (hα : α ≠ 0) (b : Fin 3 → ℝ) :
    ContDiff ℝ ∞ (axisSpatialNormalization hα b).symm := by
  have he : ((axisSpatialNormalization hα b).symm : (Fin 3 → ℝ) → Fin 3 → ℝ) =
      fun v => b+α⁻¹ • verticalRotation I (verticalRotation I v) :=
    funext (axisSpatialNormalization_symm_apply hα b)
  rw [he]
  fun_prop

theorem axisSpatialNormalization_fderiv_injective {α : ℝ} (hα : α ≠ 0)
    (b v : Fin 3 → ℝ) :
    Function.Injective (fderiv ℝ (axisSpatialNormalization hα b) v) :=
  smooth_homeomorph_fderiv_injective _ (axisSpatialNormalization_contDiff hα b)
    (axisSpatialNormalization_symm_contDiff hα b) v

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.axisSpatialNormalization_contDiff
#print axioms TwoAxisHelicoid.axisSpatialNormalization_fderiv_injective
