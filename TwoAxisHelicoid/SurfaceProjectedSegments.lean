import TwoAxisHelicoid.SurfaceProjectedAcceleration
import TwoAxisHelicoid.ClosedSurfaceTangentSegments
import TwoAxisHelicoid.UnitCurveThinTails
import TwoAxisHelicoid.ControlledCurvesTransfer

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff

private theorem surface_speed_square (v : Fin 3 → ℝ) :
    ‖coordinateToEuclidean v‖^2 = ∑ j, (v j)^2 :=
  EuclideanSpace.real_norm_sq_eq _

/-- Starting in any unit tangent direction, the projected constant field
produces an actual one-unit-time segment on the closed embedded surface.
The acceleration bound only uses curvature at the points outside the core. -/
theorem actual_surface_unit_tangent_segments {M : Type*} [TopologicalSpace M]
    (F : M → Fin 3 → ℝ) (hF : IsClosedEmbedding F)
    (e : M → OpenPartialHomeomorph M ℂ) (he : ∀ q, q ∈ (e q).source)
    (hr : ∀ q, RegularImmersionChart F (e q)) {K : Set M} {B : ℝ}
    (hB : 0 ≤ B) (hII : HasBoundedSurfaceWeingarten F e K B) :
    HasUnitTangentSegments (coordinateToTube ∘ F)
      (fun q => coordinateToTube.comp (fderiv ℝ (F ∘ (e q).symm) (e q q))) K (2*B) := by
  classical
  intro q v hv
  let D := fderiv ℝ (F ∘ (e q).symm) (e q q)
  let u := coordinateToEuclidean (D v)
  have hsq : ‖u‖^2 = 1 := by
    rw [surface_speed_square]
    simpa only [ContinuousLinearMap.comp_apply,tubeCartesian_coordinateToTube] using hv
  have hu : ‖u‖ = 1 := by nlinarith [norm_nonneg u]
  obtain ⟨V,hV,hglob,hproj⟩ := bounded_projected_surface_field F hF e he hr hII hu
  have charts (x : Fin 3 → ℝ) (hx : x ∈ range F) :
      ∃ (Y : ℂ → Fin 3 → ℝ) (z : ℂ), Y z = x ∧ ContDiffAt ℝ 2 Y z ∧
        Function.Injective (fderiv ℝ Y z) ∧ ∀ᶠ w in 𝓝 z, Y w ∈ range F ∧
          ∃ a, fderiv ℝ Y w a = V (Y w) := by
    obtain ⟨p,rfl⟩ := hx
    obtain ⟨hY,hdY⟩ := hr p _ ((e p).map_source (he p))
    refine ⟨F ∘ (e p).symm,e p p,congrArg F ((e p).left_inv (he p)),
      hY.of_le (by norm_num),hdY,?_⟩
    filter_upwards [(e p).open_target.mem_nhds ((e p).map_source (he p))] with w hw
    refine ⟨mem_range_self _,?_⟩
    simpa only [Function.comp_apply,(e p).right_inv hw] using
      projected_field_tangent_chart he hr hproj (hr p) ((e p).symm w) ((e p).map_target hw)
  obtain ⟨η,hη₀,hη⟩ := closed_surface_unit_time_orbit hF.isClosed_range hV (norm_nonneg _)
    hglob charts (mem_range_self q)
  let C := Function.extend F id (fun _ => q)
  have hC (p : M) : C (F p) = p := hF.injective.extend_apply _ _ p
  let γ := C ∘ η
  let w := fun t => coordinateToTube (V (η t))
  let a := fun t => coordinateToTube (fderiv ℝ V (η t) (V (η t)))
  have hback (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) : F (γ t) = η t := by
    obtain ⟨p,hp⟩ := (hη t ht).1
    change F (C (η t)) = η t
    rw [← hp,hC]
  have hJ (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : t ∈ Ioo (-1:ℝ) 2 :=
    ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have huT : u ∈ chartEuclideanTangent F (e q) (e q q) := ⟨v,rfl⟩
  have hinit : V (F q) = D v := surfaceCartesianEquiv.symm.injective <|
    (hproj q).trans ((chartEuclideanTangent F (e q) (e q q)).starProjection_eq_self_iff.mpr huT)
  refine ⟨γ,w,a,by simpa only [γ,Function.comp_apply,hη₀] using hC q,
    by change coordinateToTube (V (η 0)) = coordinateToTube (D v); rw [hη₀,hinit],
    ?_,?_,?_,?_⟩
  · intro t ht
    have hd := coordinateToTube.hasFDerivAt.comp_hasDerivAt t (hη t (hJ t ht)).2
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds (hJ t ht)] with s hs
    exact congrArg coordinateToTube (hback s hs)
  · intro t ht
    exact coordinateToTube.hasFDerivAt.comp_hasDerivAt t
      ((hV.differentiable one_ne_zero (η t)).hasFDerivAt.comp_hasDerivAt t (hη t (hJ t ht)).2)
  · intro t ht
    have h := (chartEuclideanTangent F (e (γ t)) (e (γ t) (γ t))).norm_starProjection_apply_le u
    rw [← hproj, hback t (hJ t ht), hu] at h
    simp only [w,tubeCartesian_coordinateToTube,← surface_speed_square]
    nlinarith [norm_nonneg (coordinateToEuclidean (V (η t)))]
  · intro t ht houtside
    have h := projected_surface_orbit_acceleration he hr hB hII hu hV hproj (γ t) houtside
    rw [hback t (hJ t ht)] at h
    simp only [a,tubeCartesian_coordinateToTube,← surface_speed_square]
    exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_surface_unit_tangent_segments
