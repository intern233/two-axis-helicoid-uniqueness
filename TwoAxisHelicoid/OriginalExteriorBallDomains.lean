import TwoAxisHelicoid.PlanarExteriorBallComponent
import TwoAxisHelicoid.MinimalExteriorBallConnectivity
import TwoAxisHelicoid.OpenPuncturedCoreConnectivity

namespace TwoAxisHelicoid
open Set Metric Filter Topology
open scoped OnePoint Topology

/-- For the original one-ended surface, after any fixed invertible
ambient linear change, every sufficiently distant ball component is
a relatively compact plane domain with connected spherical complement.
Its coordinate is taken in a single fixed chart at the actual end. -/
theorem original_far_ball_components_are_planar (s : OriginalSmoothHelicoid)
    (R : (Fin 3 → ℝ) ≃L[ℝ] (Fin 3 → ℝ)) (r : ℝ) :
    let X := coordinateToEuclidean ∘ R ∘ s.position
    ∃ (j : ℂ → OnePoint s.carrier) (B : ℝ), IsOpenEmbedding j ∧ j 0=OnePoint.infty ∧
      ∀ c : EuclideanSpace ℝ (Fin 3), B≤‖c‖ → ∀ p, p∈X ⁻¹' ball c r →
        ∃ W : Set ℂ, IsOpen W ∧ IsConnected W ∧ IsCompact (closure W) ∧
          IsPreconnected ((OnePoint.some : ℂ → OnePoint ℂ) '' W)ᶜ ∧
          j '' W=(OnePoint.some : s.carrier → OnePoint s.carrier) '' connectedComponentIn (X ⁻¹' ball c r) p := by
  intro X
  let L := s.modelTorus
  let e := s.topologicalCompactification
  let _ := periodTorus_compactSpace L
  obtain ⟨j,oj,j0,y,missing⟩ := compact_surface_open_plane_at (0 : PeriodTorus L)
  let f := e.symm ∘ j
  have emb : IsOpenEmbedding f := e.symm.isOpenEmbedding.comp oj
  have atzero : f 0=OnePoint.infty := by
    change e.symm (j 0)=OnePoint.infty
    rw [j0]
    exact e.symm_apply_apply OnePoint.infty
  have extra : ∃ w, w∉range f := ⟨e.symm y,fun ⟨z,h⟩ => missing ⟨z,e.symm.injective h⟩⟩
  let _ := punctured_complex_curve_noncompact (0 : PeriodTorus L)
  let _ : NoncompactSpace s.carrier := ⟨fun h => noncompact_univ (PuncturedPeriodTorus L) (by
    simpa only [image_univ,s.topologicalType.surjective.range_eq] using h.image s.topologicalType.continuous)⟩
  let _ := punctured_torus_is_path_connected L
  let _ : ConnectedSpace s.carrier := s.topologicalType.symm.surjective.connectedSpace s.topologicalType.symm.continuous
  have proper : IsProperMap X := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isClosedEmbedding.comp
    (R.toHomeomorph.isClosedEmbedding.comp s.closedEmbedding)).isProperMap
  obtain ⟨S,reg⟩ := original_linear_frame_harmonic_charts s R
  let _ := S
  let _ : LocallyConnectedSpace s.carrier := ChartedSpace.locallyConnectedSpace ℂ _
  let _ : LocallyCompactSpace s.carrier := ChartedSpace.locallyCompactSpace ℂ _
  have outside := one_ended_harmonic_ball_component_complement
    (homeomorphic_punctured_surface_connected_tails (0 : PeriodTorus L) s.topologicalType) proper reg
  obtain ⟨B,h⟩ := proper_far_ball_components_in_plane X proper emb ⟨0,atzero⟩ extra outside r
  exact ⟨f,B,emb,atzero,h⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_far_ball_components_are_planar
