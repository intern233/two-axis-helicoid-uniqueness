import TwoAxisHelicoid.ImmersedTangentProjection
import TwoAxisHelicoid.OrientedMinimalManifold

namespace TwoAxisHelicoid
open Complex Matrix Filter Set Topology Submodule
open scoped Topology ContDiff RealInnerProductSpace

/-- The ordinary Euclidean unit normal computed by normalizing the cross
product of the two coordinate tangent vectors of a surface chart. -/
noncomputable def euclideanUnitChartNormal (Y : ℂ → Fin 3 → ℝ) (z : ℂ) : SurfaceEuclideanSpace :=
  let c := coordinateToEuclidean (surfaceTangentCross Y z)
  ‖c‖⁻¹ • c

private theorem cartesian_tangent_cross_contDiffAt {Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hY : ContDiffAt ℝ 2 Y z) : ContDiffAt ℝ 1 (surfaceTangentCross Y) z := by
  have hd := hY.fderiv_right (m := 1) (by norm_num)
  have hh (v : ℂ) (j : Fin 3) : ContDiffAt ℝ 1 (fun w => fderiv ℝ Y w v j) z :=
    ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt).comp _ (hd.clm_apply contDiffAt_const)
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j <;> simp only [surfaceTangentCross,cross_apply] <;> exact ((hh _ _).mul (hh _ _)).sub ((hh _ _).mul (hh _ _))

private theorem euclidean_cross_ne_zero {Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hi : Function.Injective (fderiv ℝ Y z)) : coordinateToEuclidean (surfaceTangentCross Y z) ≠ 0 :=
  fun h => surfaceTangentCross_ne_zero_of_injective hi <|
    surfaceCartesianEquiv.symm.injective (h.trans coordinateToEuclidean.map_zero.symm)

theorem euclideanUnitChartNormal_contDiffAt {Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hY : ContDiffAt ℝ 2 Y z) (hi : Function.Injective (fderiv ℝ Y z)) :
    ContDiffAt ℝ 1 (euclideanUnitChartNormal Y) z := by
  have hc := coordinateToEuclidean.contDiff.contDiffAt.comp _ (cartesian_tangent_cross_contDiffAt hY)
  exact ((hc.norm ℝ (euclidean_cross_ne_zero hi)).inv (norm_ne_zero_iff.mpr (euclidean_cross_ne_zero hi))).smul hc

theorem euclideanUnitChartNormal_unit {Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hi : Function.Injective (fderiv ℝ Y z)) : ‖euclideanUnitChartNormal Y z‖ = 1 := by
  rw [euclideanUnitChartNormal,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (euclidean_cross_ne_zero hi))]

private theorem cartesian_euclidean_inner (a b : Fin 3 → ℝ) :
    ⟪coordinateToEuclidean a,coordinateToEuclidean b⟫ = a ⬝ᵥ b := by
  rw [coordinateToEuclidean_apply,coordinateToEuclidean_apply,EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct_comm]

theorem chartEuclideanTangent_iff_unitNormal {M : Type*} [TopologicalSpace M]
    {F : M → Fin 3 → ℝ} {e : OpenPartialHomeomorph M ℂ} {z : ℂ}
    (hi : Function.Injective (fderiv ℝ (F ∘ e.symm) z)) (y : SurfaceEuclideanSpace) :
    y ∈ chartEuclideanTangent F e z ↔ ⟪y,euclideanUnitChartNormal (F ∘ e.symm) z⟫ = 0 := by
  let Y := F ∘ e.symm
  let D := fderiv ℝ Y z
  let C := surfaceTangentCross Y z
  let n := euclideanUnitChartNormal Y z
  have hn : n ≠ 0 := by
    intro hz
    have hh := euclideanUnitChartNormal_unit hi
    change ‖n‖ = 1 at hh
    simp [hz] at hh
  have hle : chartEuclideanTangent F e z ≤ (ℝ ∙ n)ᗮ := by
    rintro _ ⟨v,rfl⟩
    apply mem_orthogonal_singleton_iff_inner_left.mpr
    change ⟪coordinateToEuclidean (D v), ‖coordinateToEuclidean C‖⁻¹ • coordinateToEuclidean C⟫ = 0
    rw [real_inner_smul_right,cartesian_euclidean_inner,real_linear_complex_expansion D v,
      add_dotProduct,smul_dotProduct,smul_dotProduct]
    change _ * (_ • (D 1 ⬝ᵥ D 1 ⨯₃ D I) + _ • (D I ⬝ᵥ D 1 ⨯₃ D I)) = 0
    simp
  have hr : Module.finrank ℝ (chartEuclideanTangent F e z) = 2 :=
    (LinearMap.finrank_range_of_inj (f := (coordinateToEuclidean.comp D).toLinearMap)
      (surfaceCartesianEquiv.symm.injective.comp hi)).trans Complex.finrank_real_complex
  let : Fact (Module.finrank ℝ SurfaceEuclideanSpace = 2+1) := ⟨finrank_euclideanSpace_fin⟩
  have hplane := Submodule.eq_of_le_of_finrank_eq hle
    (hr.trans (Submodule.finrank_orthogonal_span_singleton (n := 2) hn).symm)
  rw [hplane]
  exact mem_orthogonal_singleton_iff_inner_left

/-- A bound on the actual derivative of the explicitly computed chart
Gauss map off the core supplies the invariant Weingarten hypothesis.
The regular immersion itself supplies every local normal, also on the core. -/
theorem bounded_surface_weingarten_of_cross {M : Type*} [TopologicalSpace M] {F : M → Fin 3 → ℝ}
    {e : M → OpenPartialHomeomorph M ℂ} (he : ∀ q, q ∈ (e q).source)
    (hr : ∀ q, RegularImmersionChart F (e q)) {K : Set M} {B : ℝ}
    (hbound : ∀ q ∉ K, ∀ v : ℂ,
      ‖fderiv ℝ (euclideanUnitChartNormal (F ∘ (e q).symm)) (e q q) v‖ ≤
        B * ‖coordinateToEuclidean (fderiv ℝ (F ∘ (e q).symm) (e q q) v)‖) :
    HasBoundedSurfaceWeingarten F e K B := by
  intro q
  have hrq := hr q _ ((e q).map_source (he q))
  refine ⟨euclideanUnitChartNormal (F ∘ (e q).symm),
    euclideanUnitChartNormal_contDiffAt (hrq.1.of_le (by norm_num)) hrq.2,?_, hbound q⟩
  filter_upwards [(e q).open_target.mem_nhds ((e q).map_source (he q))] with w hw
  exact ⟨euclideanUnitChartNormal_unit (hr q w hw).2,chartEuclideanTangent_iff_unitNormal (hr q w hw).2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_surface_weingarten_of_cross
