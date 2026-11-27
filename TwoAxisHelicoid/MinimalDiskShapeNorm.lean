import TwoAxisHelicoid.ChartGaussianShapeIdentity

namespace TwoAxisHelicoid
open Complex Matrix Topology
open scoped RealInnerProductSpace

/-- The tangent plane contains a pair of orthonormal tangent vectors,
expressed as actual chart directions by lifting the Gram frame. -/
theorem immersed_chart_has_orthonormal_directions {D : ℂ →L[ℝ] (Fin 3 → ℝ)}
    (regular : Function.Injective D) :
    ∃ u v : ℂ, D u ⬝ᵥ D u=1 ∧ D v ⬝ᵥ D v=1 ∧ D u ⬝ᵥ D v=0 := by
  let A := D 1
  let B := D (I*1)
  let S := LinearMap.range D.toLinearMap
  have a : A∈S := ⟨1,rfl⟩
  have b : B∈S := ⟨I*1,rfl⟩
  have inS {w : Fin 3 → ℝ} (hw : w∈S) : spatialUnitVector w∈S := S.smul_mem _ hw
  obtain ⟨u,hu⟩ := inS a
  obtain ⟨v,hv⟩ := inS (S.sub_mem b (S.smul_mem ((A ⬝ᵥ B)/(A ⬝ᵥ A)) a))
  have pair := spatialGramFrame_regular regular (one_ne_zero : (1:ℂ)≠0)
  change D u=spatialUnitVector A at hu
  change D v=spatialUnitVector (B-((A ⬝ᵥ B)/(A ⬝ᵥ A)) • A) at hv
  exact ⟨u,v,by rw [hu,hv]; exact pair⟩

private theorem disk_chart_norm_sq (v : Fin 3 → ℝ) : ‖coordinateToEuclidean v‖^2=v ⬝ᵥ v := by
  rw [← real_inner_self_eq_norm_sq,coordinateToEuclidean_apply,EuclideanSpace.inner_toLp_toLp,star_trivial]

/-- In an arbitrary minimal chart the squared Hilbert–Schmidt norm
of the second fundamental form, evaluated in any orthonormal frame,
is precisely minus twice the Gaussian curvature. -/
theorem minimal_chart_squared_shape_norm {M : Type*} [TopologicalSpace M] {X : M → Fin 3 → ℝ}
    {e : OpenPartialHomeomorph M ℂ} (reg : RegularImmersionChart X e) {z : ℂ} (hz : z∈e.target)
    (minimal : coordinateMeanCurvature (X ∘ e.symm) z=0) {u v : ℂ}
    (unitU : let D := fderiv ℝ (X ∘ e.symm) z; D u ⬝ᵥ D u=1)
    (unitV : let D := fderiv ℝ (X ∘ e.symm) z; D v ⬝ᵥ D v=1) :
    let N := fderiv ℝ (euclideanUnitChartNormal (X ∘ e.symm)) z
    ‖N u‖^2+‖N v‖^2= -2*chartGaussianCurvature (X ∘ e.symm) z := by
  dsimp only
  rw [minimal_chart_gaussian_shape_identity reg hz minimal,minimal_chart_gaussian_shape_identity reg hz minimal,
    disk_chart_norm_sq,disk_chart_norm_sq,unitU,unitV]
  ring

/-- The squared Hilbert–Schmidt estimate on a minimal disk controls
the derivative of its unit normal in every tangent direction. -/
theorem minimal_disk_shape_operator_bound {M : Type*} [TopologicalSpace M] {X : M → Fin 3 → ℝ}
    {e : OpenPartialHomeomorph M ℂ} (reg : RegularImmersionChart X e) {z : ℂ} (hz : z∈e.target)
    (minimal : coordinateMeanCurvature (X ∘ e.symm) z=0) {C : ℝ} (non : 0≤C)
    (bound : let D := fderiv ℝ (X ∘ e.symm) z; let N := fderiv ℝ (euclideanUnitChartNormal (X ∘ e.symm)) z
      ∀ u v : ℂ, D u ⬝ᵥ D u=1 → D v ⬝ᵥ D v=1 → D u ⬝ᵥ D v=0 → ‖N u‖^2+‖N v‖^2≤C^2)
    (w : ℂ) : ‖fderiv ℝ (euclideanUnitChartNormal (X ∘ e.symm)) z w‖ ≤
      C*‖coordinateToEuclidean (fderiv ℝ (X ∘ e.symm) z w)‖ := by
  obtain ⟨u,v,uu,vv,uv⟩ := immersed_chart_has_orthonormal_directions (reg z hz).2
  have b := bound u v uu vv uv
  rw [minimal_chart_squared_shape_norm reg hz minimal uu vv] at b
  have k : -chartGaussianCurvature (X ∘ e.symm) z≤C^2 := by nlinarith [sq_nonneg C]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg non (norm_nonneg _))).mp
  rw [minimal_chart_gaussian_shape_identity reg hz minimal,mul_pow]
  exact mul_le_mul_of_nonneg_right k (sq_nonneg _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.minimal_disk_shape_operator_bound
