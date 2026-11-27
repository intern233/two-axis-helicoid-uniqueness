import TwoAxisHelicoid.HelicoidGraphPointGradient
import TwoAxisHelicoid.HelicoidGraphEscape
import TwoAxisHelicoid.ThinAngleParameter
import TwoAxisHelicoid.HelicoidGraphHeightDecay

namespace TwoAxisHelicoid
open Real Set Filter Bornology
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- Uniformly controlled actual tangent curves on progressively thinner
tails force the actual global graph gradient to tend to zero. -/
theorem helicoid_global_graph_gradient_decay {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {S : Set M} {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    (e : S ≃ₜ B) (he : ∀ q : S, (e q).1 = helicoidBaseCoordinates (X q.1))
    {u : B → ℝ} (hgraph : ∀ b, X (e.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2))
    (hu : ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) B)
    (hs : ∀ b, |u b| ≤ 1/2)
    (c : M → OpenPartialHomeomorph M (ℝ × ℝ))
    (hmem : ∀ q ∈ S, q ∈ (c q).source)
    (hsm : ∀ q ∈ S, ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ (c q).symm) (c q q))
    (hD : ∀ q ∈ S, Function.Injective (fderiv ℝ (X ∘ (c q).symm) (c q q)))
    (hTube : ∀ q ∈ S, X q ∈ helicoidTubeEquiv.target)
    {A : ℝ} (hA : 0 ≤ A)
    (hcurves : ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ∃ K : Set M, IsCompact K ∧
      ∀ q ∈ S, q ∉ K → HasControlledUnitTangentCurves (X q)
        (fderiv ℝ (X ∘ (c q).symm) (c q q)) ε A) :
    ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧ ∀ b : B, T < ‖b.1‖ →
      helicoidGraphGradientNorm (extendOpenScalar u) b.1 < η := by
  intro η hη
  obtain ⟨ε,hε0,hε,hsmall,hηbound⟩ := exists_small_thin_angle_parameter hA hη
  obtain ⟨K,hK,hKcurves⟩ := hcurves ε hε0 hε
  obtain ⟨T,hT,hescape⟩ := helicoid_graph_inverse_avoids_compact hX
    (fun b => (hs b).trans (by norm_num)) hgraph hK
  refine ⟨T,hT,?_⟩
  intro b hb
  have hq := (e.symm b).2
  have hd := (hu.contDiffAt (hB.mem_nhds b.2)).differentiableAt (by simp)
  exact (helicoid_global_graph_gradient_le_of_controlled_curves hB e he hgraph b hd (hs b)
    (c (e.symm b).1) (hmem _ hq) (hsm _ hq) (hTube _ hq) (hD _ hq)
    hε0 hε hA hsmall (hKcurves _ hq (hescape b hb))).trans_lt hηbound

theorem helicoid_global_graph_gradient_tendsto_zero {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (hX : Continuous X)
    {S : Set M} {B : Set (ℝ × ℝ)} (hB : IsOpen B)
    (e : S ≃ₜ B) (he : ∀ q : S, (e q).1 = helicoidBaseCoordinates (X q.1))
    {u : B → ℝ} (hgraph : ∀ b, X (e.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2))
    (hu : ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) B)
    (hs : ∀ b, |u b| ≤ 1/2)
    (c : M → OpenPartialHomeomorph M (ℝ × ℝ))
    (hmem : ∀ q ∈ S, q ∈ (c q).source)
    (hsm : ∀ q ∈ S, ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ (c q).symm) (c q q))
    (hD : ∀ q ∈ S, Function.Injective (fderiv ℝ (X ∘ (c q).symm) (c q q)))
    (hTube : ∀ q ∈ S, X q ∈ helicoidTubeEquiv.target)
    {A : ℝ} (hA : 0 ≤ A)
    (hcurves : ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ∃ K : Set M, IsCompact K ∧
      ∀ q ∈ S, q ∉ K → HasControlledUnitTangentCurves (X q)
        (fderiv ℝ (X ∘ (c q).symm) (c q q)) ε A) :
    Tendsto (fun b : B => helicoidGraphGradientNorm (extendOpenScalar u) b.1)
      (comap (Subtype.val : B → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨T,_hT,hbound⟩ := helicoid_global_graph_gradient_decay hX hB e he hgraph hu hs c
    hmem hsm hD hTube hA hcurves η hη
  have hevent : ∀ᶠ z : ℝ × ℝ in cobounded (ℝ × ℝ), T < ‖z‖ :=
    tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop T)
  apply Filter.mem_comap.mpr
  refine ⟨{z : ℝ × ℝ | T < ‖z‖},hevent,?_⟩
  intro b hb
  change dist (helicoidGraphGradientNorm (extendOpenScalar u) b.1) 0 < η
  have hnonneg : 0 ≤ helicoidGraphGradientNorm (extendOpenScalar u) b.1 := sqrt_nonneg _
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hnonneg] using hbound b hb

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoid_global_graph_gradient_tendsto_zero
