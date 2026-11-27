import TwoAxisHelicoid.PublishedFiniteTopologyCurvature
import TwoAxisHelicoid.UnmarkedPositionalGraph
import TwoAxisHelicoid.OriginalGraphExteriorNormalization

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- Check the general Meeks--Pérez hypotheses for an arbitrary embedded
one-handled minimal surface in its original coordinates. -/
theorem gaussian_bound_for_punctured_handle (mp : PublishedFiniteTopologyGaussianCurvature)
    {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {L : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L) (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (di : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ q, |chartGaussianCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)|≤C := by
  let _ : T3Space M := cl.isEmbedding.t3Space
  let _ : PathConnectedSpace (PuncturedPeriodTorus L) := punctured_torus_is_path_connected _
  let _ : ConnectedSpace M := top.symm.surjective.connectedSpace top.symm.continuous
  let _ : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  have con : ConnectedSpace (PeriodTorus L) := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)).connectedSpace
    QuotientAddGroup.continuous_mk
  have finite : HasFinitePuncturedSurfaceTopology M :=
    ⟨PeriodTorus L,inferInstance,inferInstance,periodTorus_compactSpace L,con,⟨inferInstance⟩,
      {(0:PeriodTorus L)},finite_singleton _,⟨top⟩⟩
  let Y := coordinateToEuclidean ∘ X
  have sy : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,SurfaceEuclideanSpace) 1 Y := coordinateToEuclidean.contMDiff.comp (sm.of_le (by simp))
  have iy (q : M) : Function.Injective (mvfderiv 𝓘(ℝ,ℂ) Y q) := by
    apply (NormedSpace.fromTangentSpace (𝕜 := ℝ) (Y q)).injective.comp
    change Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,SurfaceEuclideanSpace) (coordinateToEuclidean ∘ X) q)
    rw [mfderiv_comp q coordinateToEuclidean.differentiableAt.mdifferentiableAt
      (sm.mdifferentiable (by simp) q),ContinuousLinearMap.mfderiv_eq]
    exact surfaceCartesianEquiv.symm.injective.comp (di q)
  have py : IsProperMap Y := (surfaceCartesianEquiv.symm.toHomeomorph.isClosedEmbedding.comp cl).isProperMap
  exact mp M X cl.isEmbedding sm finite minimal sy iy (proper_euclideanImmersion_complete Y sy iy py)

/-- A weak single asymptotic helicoid on a one-handled original surface
determines its physical C¹ graph and an actual normalized exponential
end in its own isothermal atlas. No axis-containment hypothesis occurs. -/
theorem one_handle_positional_exterior_of_published_curvature (mp : PublishedFiniteTopologyGaussianCurvature)
    (uni : SimplyConnectedNoncompactUniformization.{0}) {M : Type} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L)
    (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X) (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (di : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0)
    {α : ℝ} (ha : α≠0) (pos : ApproachesSetAtInfinity (range X) (range (axisRuledHelicoid I α 0))) :
    HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization ha ![0,0,0] ∘ X) ∧
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ e∈atlas ℂ M, HarmonicImmersionChart X e) ∧
      ∃ A : GeometricExteriorCoordinate X, A.correction 0=0 := by
  let _ : T3Space M := cl.isEmbedding.t3Space
  obtain ⟨C,cn,bound⟩ := gaussian_bound_for_punctured_handle mp top X cl sm di minimal
  have graph := one_ended_positional_graph_of_gaussian_bound X cl sm di minimal (punctured_handle_connected_tails top)
    isCompact_empty cn (fun q _ => bound q) ha pos
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas top sm di minimal
  let _ := S
  let _ := man
  exact ⟨graph,S,man,charts,one_handle_original_frame_exterior top uni X cl charts ha graph⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.gaussian_bound_for_punctured_handle
#print axioms TwoAxisHelicoid.one_handle_positional_exterior_of_published_curvature
