import TwoAxisHelicoid.FlatCapSmoothAtlas
import TwoAxisHelicoid.FlatCapOriginalManifold
import TwoAxisHelicoid.ImmersionChartReparametrization

namespace TwoAxisHelicoid
open Set Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

/-- The cap's constructed atlas agrees smoothly with the original
complex atlas on the entire punctured surface. No compatibility at the
added point is assumed or asserted. -/
theorem punctured_flat_cap_smooth_atlas_compatible
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {p : M} {X₀ : M → HelicoidTubeCoordinates}
    (hX : IsProperMap (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hXi : Function.Injective (fun q : {q : M // q ≠ p} => X₀ q.1))
    {A H R : ℝ} (hR : 0 < R) (hA1 : 1 ≤ A) (hAR : 4*R^2 ≤ A) (hH : 4*R ≤ H)
    (hexact : ∀ y, R^2 < ambientRadiusSq y →
      (y ∈ range (fun q : {q : M // q ≠ p} => X₀ q.1) ↔ y.1.2 = 0))
    (hsm : ∀ x ≠ p, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ X₀ x)
    (hi : ∀ x ≠ p, Function.Injective
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) X₀ x)) :
    let F := puncturedCapMap p A H (fun q : {q : M // q ≠ p} => X₀ q.1)
    ∃ cs : ChartedSpace (ℝ × ℝ) M, let _ := cs
      IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M ∧ IsClosedEmbedding F ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F ∧
      (∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) F x)) ∧
      ∀ x ≠ p, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F x ∧
        Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) F x) ∧
        ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id M) x ∧
        ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id M) x := by
  let F := puncturedCapMap p A H (fun q : {q : M // q ≠ p} => X₀ q.1)
  obtain ⟨cs,hm,hclosed,hcap,hcapi⟩ := punctured_flat_cap_has_smooth_atlas
    hX hXi hR hA1 hAR hH hexact (punctured_complex_immersion_real_charts hsm hi)
  let _ := cs
  let _ := hm
  refine ⟨cs,hm,hclosed,hcap,hcapi,?_⟩
  intro x hx
  have hEq : ∀ q ≠ p, F q = ambientPlaneCap A H (X₀ q) := by
    intro q hq
    exact puncturedCapMap_on_punctured p A H _ ⟨q,hq⟩
  have hflat : ∀ q ≠ p, R^2 < ambientRadiusSq (X₀ q) → (X₀ q).1.2 = 0 := by
    intro q hq hr
    exact (hexact (X₀ q) hr).mp ⟨⟨q,hq⟩,rfl⟩
  obtain ⟨ho,hoi⟩ := actual_flat_cap_original_manifold_regular hx (hsm x hx) (hi x hx)
    hR hA1 hAR hH hEq hflat
  exact ⟨ho,hoi,common_immersion_structures_compatible ho hoi (hcap x) (hcapi x)⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.punctured_flat_cap_smooth_atlas_compatible
