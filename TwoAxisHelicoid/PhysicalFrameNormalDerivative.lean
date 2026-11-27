import TwoAxisHelicoid.ReferenceHelicoidEnd
import TwoAxisHelicoid.ChartSecondFundamentalWeingarten

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology ContDiff

private noncomputable def horizontalHalfTurn : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (verticalRotation I).comp (verticalRotation I)

private theorem horizontalHalfTurn_apply (v : Fin 3 → ℝ) :
    horizontalHalfTurn v= ![-v 0,-v 1,v 2] := by
  ext j
  fin_cases j <;> simp [horizontalHalfTurn,verticalRotation_apply]

private theorem horizontalHalfTurn_cross (v w : Fin 3 → ℝ) :
    horizontalHalfTurn v ⨯₃ horizontalHalfTurn w=horizontalHalfTurn (v ⨯₃ w) := by
  ext j
  fin_cases j <;> simp [horizontalHalfTurn_apply,cross_apply] <;> ring

private noncomputable def euclideanHorizontalHalfTurn : SurfaceEuclideanSpace →L[ℝ] SurfaceEuclideanSpace :=
  coordinateToEuclidean.comp (horizontalHalfTurn.comp surfaceCartesianEquiv.toContinuousLinearMap)

private theorem euclideanHalfTurn_apply_cartesian (v : Fin 3 → ℝ) :
    euclideanHorizontalHalfTurn (coordinateToEuclidean v)=coordinateToEuclidean (horizontalHalfTurn v) := by
  change coordinateToEuclidean (horizontalHalfTurn (surfaceCartesianEquiv (coordinateToEuclidean v)))=_
  rw [surfaceCartesian_toEuclidean]

private theorem euclideanHalfTurn_norm (v : SurfaceEuclideanSpace) : ‖euclideanHorizontalHalfTurn v‖=‖v‖ := by
  obtain ⟨w,rfl⟩ : ∃ w, coordinateToEuclidean w=v := ⟨_,surfaceEuclidean_toCartesian v⟩
  rw [euclideanHalfTurn_apply_cartesian]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,horizontalHalfTurn_apply]
  simp [Fin.sum_univ_succ]

private theorem centered_frame_value {α : ℝ} (ha : α≠0) (v : Fin 3 → ℝ) :
    centeredHelicoidNormalization ha v=α • horizontalHalfTurn v := by
  change axisSpatialNormalization ha 0 v=_
  rw [axisSpatialNormalization_apply,map_zero,sub_zero,map_smul]
  rfl

private theorem centered_frame_normal {α : ℝ} (ha : α≠0) {Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (dy : DifferentiableAt ℝ Y z) :
    euclideanUnitChartNormal (centeredHelicoidNormalization ha ∘ Y) z =
      euclideanHorizontalHalfTurn (euclideanUnitChartNormal Y z) := by
  let R := centeredHelicoidNormalization ha
  let D := fderiv ℝ Y z
  have d := (R.toContinuousLinearMap.hasFDerivAt.comp z dy.hasFDerivAt).fderiv
  have cross : coordinateToEuclidean (surfaceTangentCross (R ∘ Y) z)=α^2 • euclideanHorizontalHalfTurn (coordinateToEuclidean (surfaceTangentCross Y z)) := by
    rw [euclideanHalfTurn_apply_cartesian]
    unfold surfaceTangentCross
    change coordinateToEuclidean (fderiv ℝ (R.toContinuousLinearMap ∘ Y) z 1 ⨯₃ fderiv ℝ (R.toContinuousLinearMap ∘ Y) z I)=_
    rw [d]
    change coordinateToEuclidean (R (D 1) ⨯₃ R (D I))=α^2 • coordinateToEuclidean (horizontalHalfTurn (D 1 ⨯₃ D I))
    rw [centered_frame_value,centered_frame_value]
    have h : (α • horizontalHalfTurn (D 1)) ⨯₃ (α • horizontalHalfTurn (D I)) =
        α^2 • (horizontalHalfTurn (D 1) ⨯₃ horizontalHalfTurn (D I)) := by
      ext j
      fin_cases j <;> simp [cross_apply] <;> ring
    rw [h,horizontalHalfTurn_cross,map_smul]
  let C := coordinateToEuclidean (surfaceTangentCross Y z)
  change ‖coordinateToEuclidean (surfaceTangentCross (R ∘ Y) z)‖⁻¹ • coordinateToEuclidean (surfaceTangentCross (R ∘ Y) z)=
    euclideanHorizontalHalfTurn (‖C‖⁻¹ • C)
  rw [cross,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),euclideanHalfTurn_norm,map_smul,smul_smul]
  change ((α^2*‖C‖)⁻¹*α^2) • euclideanHorizontalHalfTurn C=‖C‖⁻¹ • euclideanHorizontalHalfTurn C
  rw [_root_.mul_inv_rev,mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ ha),mul_one]

/-- Under the physical pitch normalization the differential of the unit
normal keeps its Euclidean length and each spatial tangent length is
multiplied by the absolute pitch. This is valid for both pitch signs. -/
theorem physical_frame_normal_derivative_lengths {α : ℝ} (ha : α≠0)
    {P : Type*} [TopologicalSpace P] {X : P → Fin 3 → ℝ} {e : OpenPartialHomeomorph P ℂ}
    (reg : RegularImmersionChart X e) {z : ℂ} (hz : z∈e.target) (v : ℂ) :
    let R := centeredHelicoidNormalization ha
    let Y := X ∘ e.symm
    ‖fderiv ℝ (euclideanUnitChartNormal (R ∘ Y)) z v‖=‖fderiv ℝ (euclideanUnitChartNormal Y) z v‖ ∧
      ‖coordinateToEuclidean (fderiv ℝ (R ∘ Y) z v)‖=|α| *‖coordinateToEuclidean (fderiv ℝ Y z v)‖ := by
  let R := centeredHelicoidNormalization ha
  let Y := X ∘ e.symm
  have germ : euclideanUnitChartNormal (R ∘ Y) =ᶠ[𝓝 z] euclideanHorizontalHalfTurn ∘ euclideanUnitChartNormal Y := by
    filter_upwards [e.open_target.mem_nhds hz] with q hq
    exact centered_frame_normal ha ((reg q hq).1.differentiableAt (by simp))
  have dn := (euclideanUnitChartNormal_contDiffAt ((reg z hz).1.of_le (by norm_num)) (reg z hz).2).differentiableAt_one
  have de := (euclideanHorizontalHalfTurn.hasFDerivAt.comp z dn.hasFDerivAt).fderiv
  have dt := (R.toContinuousLinearMap.hasFDerivAt.comp z ((reg z hz).1.differentiableAt (by simp)).hasFDerivAt).fderiv
  constructor
  · change ‖fderiv ℝ (euclideanUnitChartNormal (R ∘ Y)) z v‖=_
    rw [germ.fderiv_eq,de]
    exact euclideanHalfTurn_norm _
  · change ‖coordinateToEuclidean (fderiv ℝ (R.toContinuousLinearMap ∘ Y) z v)‖=_
    rw [dt]
    change ‖coordinateToEuclidean (R (fderiv ℝ Y z v))‖=_
    rw [centered_frame_value,map_smul,norm_smul,Real.norm_eq_abs,← euclideanHalfTurn_apply_cartesian,euclideanHalfTurn_norm]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_frame_normal_derivative_lengths
