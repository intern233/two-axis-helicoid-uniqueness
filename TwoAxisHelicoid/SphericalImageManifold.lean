import TwoAxisHelicoid.SphericalImageChart
import TwoAxisHelicoid.ImmersionAtlasMap

namespace TwoAxisHelicoid
open Set Topology
open scoped Topology ContDiff Manifold

/-- The sphere chart at the added point and all actual finite-point
charts give a full compatible smooth structure on the original compact
topological space, in which the embedded ambient map is an immersion. -/
theorem spherical_image_has_smooth_immersion_atlas
    {M : Type*} [TopologicalSpace M] {F : M → HelicoidTubeCoordinates}
    (hF : IsEmbedding F) {p : M} {H : ℝ} (hH : 0 < H)
    (hp : F p = planeCapNorth H) {W : Set HelicoidTubeCoordinates}
    (hW : IsOpen W) (hpW : planeCapNorth H ∈ W)
    (himage : range F ∩ W = planeCapSphere H ∩ W)
    (hfinite : ∀ x ≠ p, ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      RegularImmersionChart F e ∧ x ∈ e.source) :
    ∃ cs : ChartedSpace (ℝ × ℝ) M, let _ := cs
      IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F ∧
      ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) F x) := by
  obtain ⟨ep,hep,hpep,_hep0⟩ :=
    exists_regular_chart_of_spherical_image hF hH hp hW hpW himage
  have hcover (x : M) : ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      RegularImmersionChart F e ∧ x ∈ e.source := by
    by_cases hx : x = p
    · exact ⟨ep,hep,hx ▸ hpep⟩
    · exact hfinite x hx
  refine ⟨immersionAtlasChartedSpace F hcover,?_⟩
  exact ⟨immersionAtlas_isManifold F hcover,
    immersionAtlas_map_contMDiff F hF.continuous hcover,
    immersionAtlas_map_mfderiv_injective F hF.continuous hcover⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.spherical_image_has_smooth_immersion_atlas
