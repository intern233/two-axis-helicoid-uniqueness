import TwoAxisHelicoid.HelicoidCapSmoothAtlas
import TwoAxisHelicoid.ImmersionChartReparametrization

namespace TwoAxisHelicoid
open Set Topology
open scoped ContDiff Manifold

/-- Capping for the actual punctured complex-manifold immersion. Its
finite-point charts are obtained from the original standard manifold
smoothness and derivative; the new point is handled by the proved
spherical chart construction. -/
theorem HasHelicoidC1End.exists_smooth_cap_from_complex_immersion
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
      (cs : ChartedSpace (ℝ × ℝ) M), let _ := cs
      let F := helicoidCompactCap p D R (fun q : {q : M // q ≠ p} => X₀ q.1)
      0 < R ∧ IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ M ∧ IsClosedEmbedding F ∧
      ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F ∧
      (∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) F x)) ∧
      ∀ q ∈ C, F q.1 = X₀ q.1 :=
  hEnd.exists_smooth_compact_cap_fixing_core hX hXi
    (punctured_complex_immersion_real_charts hsm hi) hC

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidC1End.exists_smooth_cap_from_complex_immersion
