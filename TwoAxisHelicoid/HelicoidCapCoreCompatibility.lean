import TwoAxisHelicoid.HelicoidManifoldCap
import TwoAxisHelicoid.CommonImmersionSmoothStructures
import TwoAxisHelicoid.PuncturedCompactNeighborhood

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

/-- The actual smooth cap can fix a whole neighborhood of any compact
core. On that neighborhood, the original and cap smooth structures are
mutually smooth through the identity on their common parameter space. -/
theorem HasHelicoidC1End.exists_smooth_cap_compatible_near_core
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {p : M} {X₀ : M → HelicoidTubeCoordinates}
    (hEnd : HasHelicoidC1End (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hX : IsProperMap (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hXi : Function.Injective (fun q : {q : M // q ≠ p} => X₀ q.1))
    (hsm : ∀ x ≠ p, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ X₀ x)
    (hi : ∀ x ≠ p, Function.Injective
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,HelicoidTubeCoordinates) X₀ x))
    {C : Set {q : M // q ≠ p}} (hC : IsCompact C) :
    ∃ (D : HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates) (R : ℝ)
      (cs : ChartedSpace (ℝ × ℝ) M) (U : Set M), let _ := cs
      let F := helicoidCompactCap p D R (fun q : {q : M // q ≠ p} => X₀ q.1)
      0 < R ∧ IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M ∧ IsClosedEmbedding F ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F ∧
      (∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) F x)) ∧
      IsOpen U ∧ p ∉ U ∧ Subtype.val '' C ⊆ U ∧
      (∀ x ∈ U, F x = X₀ x) ∧
      ∀ x ∈ U, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id M) x ∧
        ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id M) x := by
  obtain ⟨K,U,hK,hU,hpU,hCU,hUK⟩ := punctured_compact_core_neighborhood hC
  obtain ⟨D,R,cs,hR,hm,hclosed,hcap,hcapi,hfix⟩ :=
    hEnd.exists_smooth_cap_from_complex_immersion hX hXi hsm hi hK
  let _ := cs
  let _ := hm
  let F := helicoidCompactCap p D R (fun q : {q : M // q ≠ p} => X₀ q.1)
  have hFU : ∀ x ∈ U, F x = X₀ x := by
    intro x hx
    obtain ⟨q,hq,hqx⟩ := hUK hx
    rw [← hqx]
    exact hfix q hq
  refine ⟨D,R,cs,U,hR,hm,hclosed,hcap,hcapi,hU,hpU,hCU,hFU,?_⟩
  intro x hx
  have hxp : x ≠ p := fun he => hpU (he ▸ hx)
  have heq : F =ᶠ[𝓝 x] X₀ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hFU y hy
  exact locally_fixed_cap_structures_compatible heq (hsm x hxp) (hi x hxp)
    (hcap x) (hcapi x)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidC1End.exists_smooth_cap_compatible_near_core
