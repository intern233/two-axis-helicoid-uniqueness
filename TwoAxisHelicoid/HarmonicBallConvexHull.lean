import TwoAxisHelicoid.CompactMinimalBallHull
import TwoAxisHelicoid.OriginalHelicoidMetric
import TwoAxisHelicoid.PuncturedTorusRealOrientation

namespace TwoAxisHelicoid
open Set Metric Topology InnerProductSpace
open scoped ContDiff Manifold

/-- Isothermal charts for the original surface also supply regular
harmonic coordinates after a fixed invertible ambient linear map. -/
theorem original_linear_frame_harmonic_charts (s : OriginalSmoothHelicoid)
    (R : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)) :
    ∃ S : ChartedSpace ℂ s.carrier, ∀ p, let e := S.chartAt p
      let F := (coordinateToEuclidean ∘ R ∘ s.position) ∘ e.symm
      HarmonicAt F (e p) ∧ Function.Injective (fderiv ℝ F (e p)) := by
  obtain ⟨S,_,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas s.topologicalType s.smooth s.immersion s.minimal
  refine ⟨S,fun p => ?_⟩
  let e := S.chartAt p
  let T := coordinateToEuclidean.comp R.toContinuousLinearMap
  let Y := s.position ∘ e.symm
  obtain ⟨hh,_,hi⟩ := charts e (S.chart_mem_atlas p) (e p) (e.map_source (S.mem_chart_source p))
  have harm : HarmonicAt Y (e p) := spatial_harmonic_of_coordinates hh
  refine ⟨harm.comp_CLM T,?_⟩
  change Function.Injective (fderiv ℝ (T ∘ Y) (e p))
  rw [(T.hasFDerivAt.comp _ (harm.1.differentiableAt two_ne_zero).hasFDerivAt).fderiv]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective.comp (R.injective.comp hi)

/-- Every compact part of the original surface stays inside any
closed spatial ball containing its topological boundary. -/
theorem original_compact_region_inside_boundary_ball (s : OriginalSmoothHelicoid) (K : Set s.carrier)
    (compact : IsCompact K) (o : EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (boundary : ∀ q∈frontier K, dist (s.euclideanPosition q) o≤r) :
    ∀ q∈K, dist (s.euclideanPosition q) o≤r := by
  obtain ⟨S,reg⟩ := original_linear_frame_harmonic_charts s (ContinuousLinearEquiv.refl ℝ _)
  let _ := S
  exact fun q hq => compact_harmonic_patch_ball_hull s.euclidean_proper.continuous reg compact (fun p hp => boundary p hp) hq

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_linear_frame_harmonic_charts
#print axioms TwoAxisHelicoid.original_compact_region_inside_boundary_ball
