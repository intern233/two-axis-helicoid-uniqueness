import TwoAxisHelicoid.MarkedDiskGreenExistence
import TwoAxisHelicoid.CompactPlanarRealization

namespace TwoAxisHelicoid
open Complex Set Metric Filter Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

universe u

/-- Every compact part of any topological-plane Riemann surface lies
in a single univalent holomorphic chart. Its marked round neighborhood
is uniformized by its constructed Green function. -/
theorem topological_plane_has_compact_coordinates {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] (T : M ≃ₜ ℂ) : HasPlanarCoordinatesOnCompacts M := by
  classical
  let _ : T2Space M := T.isEmbedding.t2Space
  intro K ck
  obtain ⟨C,bd⟩ := (ck.image T.continuous).isBounded.exists_norm_le
  let R := max C 0+1
  have rp : 0<R := by dsimp [R]; linarith [le_max_right C 0]
  let V := markedBallDomain T R
  obtain ⟨p,ρ,hρ⟩ := marked_disk_dirichlet_green T rp
  obtain ⟨f,hf,inj,_,_⟩ := disk_coordinate_from_green_modulus (markedBallPlaneHomeomorph T rp) hρ
  obtain ⟨S,E,_⟩ := biholomorphic_coordinate_range inj (univalent_surface_local_biholomorphism hf inj)
  obtain ⟨e,src,_,eh⟩ := holomorphic_subdomain_coordinate V S ⟨p⟩ E
  refine ⟨e.source,e,e.open_source,fun x hx => ?_,fun x hx => (contMDiffAt_of_mem_maximalAtlas eh hx).contMDiffWithinAt,e.injOn⟩
  rw [src]
  apply mem_ball_zero_iff.mpr
  have h := bd _ (mem_image_of_mem T hx)
  dsimp only [R]; linarith [le_max_left C 0]

/-- Uniformization of the topological plane for an arbitrary compatible
complex atlas, including both the parabolic and hyperbolic alternatives. -/
theorem topological_plane_uniformization_proved : TopologicalPlaneUniformization.{u} :=
  plane_uniformization_of_univalent_function fun _ _ _ _ home =>
    topological_plane_univalent_of_compact_coordinates home.some (topological_plane_has_compact_coordinates home.some)

/-- The conformal classification of arbitrary abstract annuli used in
TwoAxisHelicoid, with no uniformization hypothesis. -/
theorem annular_riemann_surface_uniformization_proved : AnnularRiemannSurfaceUniformization.{u} :=
  annular_classification_of_plane_uniformization topological_plane_uniformization_proved

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.topological_plane_uniformization_proved
#print axioms TwoAxisHelicoid.annular_riemann_surface_uniformization_proved
