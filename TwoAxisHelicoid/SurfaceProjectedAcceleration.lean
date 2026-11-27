import TwoAxisHelicoid.BoundedProjectedSurfaceField

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- A derivative in each coordinate direction of the genuine projected
field is controlled by the derivative of the local Euclidean normal. -/
theorem projected_field_directional_derivative {f n : ℂ → SurfaceEuclideanSpace} {z : ℂ}
    {u : SurfaceEuclideanSpace} (hu : ‖u‖ = 1) (hn : ‖n z‖ = 1)
    (hf : DifferentiableAt ℝ f z) (hd : DifferentiableAt ℝ n z)
    (he : f =ᶠ[𝓝 z] fun w => projectedTangentVelocity u (n w)) (v : ℂ) :
    ‖fderiv ℝ f z v‖ ≤ 2*‖fderiv ℝ n z v‖ := by
  let l := fun t : ℝ => z+t • v
  have hl : HasDerivAt l v 0 := by
    simpa only [l,id_eq,zero_add,one_smul] using (hasDerivAt_const (0:ℝ) z).fun_add ((hasDerivAt_id (0:ℝ)).smul_const v)
  have h0 : l 0 = z := by simp [l]
  have hf' : HasFDerivAt f (fderiv ℝ f z) (l 0) := h0.symm ▸ hf.hasFDerivAt
  have hd' : HasFDerivAt n (fderiv ℝ n z) (l 0) := h0.symm ▸ hd.hasFDerivAt
  obtain ⟨a,ha,hb⟩ := projectedTangentVelocity_derivative_bound (hd'.comp_hasDerivAt 0 hl) hu (by change ‖n (l 0)‖ = 1; rwa [h0])
  have hh : f ∘ l =ᶠ[𝓝 (0:ℝ)] (fun t => projectedTangentVelocity u ((n ∘ l) t)) :=
    (h0 ▸ hl.continuousAt.tendsto : Tendsto l (𝓝 0) (𝓝 z)).eventually he
  have heq := (hf'.comp_hasDerivAt 0 hl).unique (ha.congr_of_eventuallyEq hh)
  rwa [heq]

/-- The acceleration of the ambient extended field in its own tangent
direction at a surface point is at most twice the Weingarten bound. -/
theorem projected_surface_orbit_acceleration {M : Type*} [TopologicalSpace M] {F : M → Fin 3 → ℝ}
    {e : M → OpenPartialHomeomorph M ℂ} (he : ∀ q, q ∈ (e q).source)
    (hr : ∀ q, RegularImmersionChart F (e q)) {K : Set M} {B : ℝ} (hB : 0 ≤ B)
    (hII : HasBoundedSurfaceWeingarten F e K B) {u : SurfaceEuclideanSpace} (hu : ‖u‖ = 1)
    {V : (Fin 3 → ℝ) → Fin 3 → ℝ} (hV : ContDiff ℝ 1 V)
    (hproj : ∀ q, coordinateToEuclidean (V (F q)) = (chartEuclideanTangent F (e q) (e q q)).starProjection u)
    (q : M) (hq : q ∉ K) :
    ‖coordinateToEuclidean (fderiv ℝ V (F q) (V (F q)))‖ ≤ 2*B := by
  let z := e q q
  let Y := F ∘ (e q).symm
  let G := coordinateToEuclidean ∘ V ∘ Y
  have hy : Y z = F q := congrArg F ((e q).left_inv (he q))
  have hY := (hr q z ((e q).map_source (he q))).1.differentiableAt (by simp)
  have hV' : HasFDerivAt V (fderiv ℝ V (F q)) (Y z) :=
    hy.symm ▸ (hV.differentiable one_ne_zero (F q)).hasFDerivAt
  have hg : HasFDerivAt G (coordinateToEuclidean.comp ((fderiv ℝ V (F q)).comp (fderiv ℝ Y z))) z :=
    coordinateToEuclidean.hasFDerivAt.comp z (hV'.comp z hY.hasFDerivAt)
  obtain ⟨n,hn,hc,hbound⟩ := hII q
  have hG : G =ᶠ[𝓝 z] fun w => projectedTangentVelocity u (n w) := by
    filter_upwards [surface_projection_chart_germ he hr q u hc] with w hw
    exact (hproj ((e q).symm w)).trans hw
  obtain ⟨a,ha⟩ := projected_field_tangent_chart he hr hproj (hr q) q (he q)
  have h := projected_field_directional_derivative hu hc.self_of_nhds.1 hg.differentiableAt hn.differentiableAt_one hG a
  rw [hg.fderiv] at h
  change ‖coordinateToEuclidean (fderiv ℝ V (F q) (fderiv ℝ Y z a))‖ ≤ _ at h
  change fderiv ℝ Y z a = V (F q) at ha
  rw [ha] at h
  have hb := hbound hq a
  change ‖fderiv ℝ n z a‖ ≤ B*‖coordinateToEuclidean (fderiv ℝ Y z a)‖ at hb
  rw [ha,hproj] at hb
  have hspeed := (chartEuclideanTangent F (e q) (e q q)).norm_starProjection_apply_le u
  rw [hu] at hspeed
  exact h.trans (mul_le_mul_of_nonneg_left
    (hb.trans ((mul_le_mul_of_nonneg_left hspeed hB).trans_eq (mul_one _))) (by norm_num))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.projected_surface_orbit_acceleration
