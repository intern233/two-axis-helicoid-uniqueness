import TwoAxisHelicoid.PositionalBoundedCurvatureGraph
import TwoAxisHelicoid.ChartGaussianShapeIdentity
import TwoAxisHelicoid.PhysicalFrameNormalDerivative

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff Manifold

/-- A one-ended properly embedded minimal surface with bounded Gaussian
curvature off a compact set and one-sided positional convergence to a
helicoid has a single C¹ graph end. No straight line on the surface or
genus restriction is required. -/
theorem one_ended_positional_graph_of_gaussian_bound {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (di : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0)
    (one : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K)
    {K : Set M} (kc : IsCompact K) {C : ℝ} (nonneg : 0≤C)
    (bound : ∀ q∉K, |chartGaussianCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)|≤C)
    {α : ℝ} (ha : α≠0) (pos : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I α 0))) :
    HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ X) := by
  let A := centeredHelicoidNormalization ha
  let Y := A ∘ X
  have hz : (![0,0,0] : Fin 3 → ℝ)=0 := by ext j; fin_cases j <;> rfl
  rw [hz]
  change HasHelicoidC1End (coordinateToTube ∘ Y)
  have closed : IsClosedEmbedding Y := A.toHomeomorph.isClosedEmbedding.comp cl
  have sa : ContMDiff 𝓘(ℝ,Fin 3 → ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ A.toContinuousLinearMap := A.toContinuousLinearMap.contMDiff
  have sy : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ Y := sa.comp sm
  have iy (q : M) : Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) Y q) := by
    change Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (A.toContinuousLinearMap ∘ X) q)
    rw [mfderiv_comp q (sa.mdifferentiable (by simp) _) (sm.mdifferentiable (by simp) _),
      mfderiv_eq_fderiv,A.toContinuousLinearMap.hasFDerivAt.fderiv]
    exact A.injective.comp (di q)
  apply general_thin_tube_lemma_4_3 Y closed.isProperMap closed.injective sy iy one kc
    (div_nonneg (Real.sqrt_nonneg C) (abs_nonneg α)) _ (positional_standard_end_actual_tubes closed.isProperMap
      (reference_frame_positional_standard _ ha pos))
  intro q hq v
  let e := chartAt ℂ q
  let Z := X ∘ e.symm
  have reg := smooth_surface_regular_manifold_chart sm di q
  have inside : e q∈e.target := e.map_source (mem_chart_source ℂ q)
  obtain ⟨n,t⟩ := physical_frame_normal_derivative_lengths ha reg inside v
  have estimate := minimal_gaussian_bound_implies_shape_bound reg inside (minimal q) nonneg (bound q hq) v
  change ‖fderiv ℝ (euclideanUnitChartNormal (A ∘ Z)) (e q) v‖≤Real.sqrt C/|α| *
    ‖coordinateToEuclidean (fderiv ℝ (A ∘ Z) (e q) v)‖
  rw [n,t,← mul_assoc,div_mul_cancel₀ _ (abs_ne_zero.mpr ha)]
  exact estimate

theorem punctured_handle_connected_tails {M : Type*} [TopologicalSpace M] {L : PeriodPair}
    (top : M ≃ₜ PuncturedPeriodTorus L) (K : Set M) (kc : IsCompact K) :
    ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K := by
  let _ := punctured_complex_curve_noncompact (0:PeriodTorus L)
  have ncmp : NoncompactSpace M := ⟨fun h => noncompact_univ (PuncturedPeriodTorus L) (by
    simpa only [image_univ,top.surjective.range_eq] using h.image top.continuous)⟩
  obtain ⟨U,conn,k,d⟩ := homeomorphic_punctured_surface_connected_tails (0:PeriodTorus L) top K kc
  have inhabited : U.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h,compl_empty] at k
    exact noncompact_univ M k
  exact ⟨U,⟨inhabited,conn⟩,k,d⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.one_ended_positional_graph_of_gaussian_bound
#print axioms TwoAxisHelicoid.punctured_handle_connected_tails
