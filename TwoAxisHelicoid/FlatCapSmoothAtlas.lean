import TwoAxisHelicoid.SphericalImageManifold
import TwoAxisHelicoid.RegularCapChart
import TwoAxisHelicoid.PuncturedCapMap
import TwoAxisHelicoid.FlatEndCapNeighborhood

namespace TwoAxisHelicoid
open Real Set Topology
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1000000

/-- The concrete compact capping map has a full smooth immersion atlas.
Only the uncapped finite-point charts are input. The chart at the added
point and compatibility of the entire new atlas are proved. -/
theorem punctured_flat_cap_has_smooth_atlas
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    {p : M} {X₀ : M → HelicoidTubeCoordinates}
    (hX : IsProperMap (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hXi : Function.Injective (fun q : {q : M // q ≠ p} => X₀ q.1))
    {A H R : ℝ} (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hexact : ∀ y, R^2 < ambientRadiusSq y →
      (y ∈ range (fun q : {q : M // q ≠ p} => X₀ q.1) ↔ y.1.2 = 0))
    (hfinite : ∀ x ≠ p, ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      RegularImmersionChart X₀ e ∧ p ∉ e.source ∧ x ∈ e.source) :
    let F := puncturedCapMap p A H (fun q : {q : M // q ≠ p} => X₀ q.1)
    ∃ cs : ChartedSpace (ℝ × ℝ) M, let _ := cs
      IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M ∧
      IsClosedEmbedding F ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F ∧
      ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) F x) := by
  let X : {q : M // q ≠ p} → HelicoidTubeCoordinates := fun q => X₀ q.1
  let F := puncturedCapMap p A H X
  have hflat : ∀ y ∈ range X, R^2 < ambientRadiusSq y → y.1.2 = 0 :=
    fun y hy hr => (hexact y hr).mp hy
  have hF : IsClosedEmbedding F :=
    puncturedCapMap_isClosedEmbedding hX hXi hR hA1 hAR hH hflat
  have hHpos : 0 < H := by linarith
  obtain ⟨W,hW,hpW,hWs⟩ := cappedOnePointMap_spherical_neighborhood
    hR hA1 hAR hH hexact
  have hrange : range F = range (cappedOnePointMap A H X) :=
    (punctureOnePointHomeomorph p).symm.surjective.range_comp _
  have hFs : range F ∩ W = planeCapSphere H ∩ W := by rw [hrange,hWs]
  have hFp : F p = planeCapNorth H := puncturedCapMap_at_puncture p A H X
  have hEq (x : M) (hx : x ≠ p) : F x = ambientPlaneCap A H (X₀ x) :=
    puncturedCapMap_on_punctured p A H X ⟨x,hx⟩
  have hreg (x : M) (hx : x ≠ p) : ∃ e : OpenPartialHomeomorph M (ℝ × ℝ),
      RegularImmersionChart F e ∧ x ∈ e.source := by
    obtain ⟨e,he,hpe,hxe⟩ := hfinite x hx
    refine ⟨e,ambient_cap_regular_chart e he hpe hR hA1 hAR hH hEq ?_,hxe⟩
    intro q hq hr
    exact hflat (X₀ q) ⟨⟨q,hq⟩,rfl⟩ hr
  obtain ⟨cs,hm,hsm,hdi⟩ :=
    spherical_image_has_smooth_immersion_atlas hF.isEmbedding hHpos hFp hW hpW hFs hreg
  exact ⟨cs,hm,hF,hsm,hdi⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_flat_cap_has_smooth_atlas
