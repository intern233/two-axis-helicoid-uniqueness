import TwoAxisHelicoid.ControlledThinEndC1Graph

namespace TwoAxisHelicoid
open Real Set Filter Bornology
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- The C¹ graph conclusion only needs charts on the end outside one
fixed compact core. This permits the actual height chart of an analytic
end; no extension of that chart through the handles is required. -/
theorem controlled_thin_tail_C1_normal_graph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M] [T2Space M]
    (p : M) {X : {q : M // q ≠ p} → HelicoidTubeCoordinates}
    (hp : IsProperMap X) {K₀ : Set {q : M // q ≠ p}}
    (hX : InjOn X K₀ᶜ) (hK₀ : IsCompact K₀)
    (c : {q : M // q ≠ p} → OpenPartialHomeomorph {q : M // q ≠ p} (ℝ × ℝ))
    (hmem : ∀ q ∉ K₀, q ∈ (c q).source)
    (hsm : ∀ q ∉ K₀, ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ (c q).symm) (c q q))
    (hD : ∀ q ∉ K₀, Function.Injective (fderiv ℝ (X ∘ (c q).symm) (c q q)))
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ K : Set {q : M // q ≠ p}, IsCompact K ∧
      ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target ∧ |helicoidSignedDistance (X q)| ≤ ε)
    {A : ℝ} (hA : 0 ≤ A)
    (hcurves : ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ∃ K : Set {q : M // q ≠ p}, IsCompact K ∧
      ∀ q ∉ K, HasControlledUnitTangentCurves (X q)
        (fderiv ℝ (X ∘ (c q).symm) (c q q)) ε A) :
    ∃ K : Set {q : M // q ≠ p}, IsCompact K ∧ ∃ R : ℝ, 0 < R ∧
      IsCompact (helicoidProjectedEnd X K (exteriorPlaneBase R))ᶜ ∧
      ∃ e : helicoidProjectedEnd X K (exteriorPlaneBase R) ≃ₜ exteriorPlaneBase R,
        (e : helicoidProjectedEnd X K (exteriorPlaneBase R) → exteriorPlaneBase R) =
          helicoidEndProjection X K (exteriorPlaneBase R) ∧
        ∃ u : exteriorPlaneBase R → ℝ,
          ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R) ∧
          (∀ b, |u b| ≤ 1/2 ∧ X (e.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2)) ∧
          Tendsto (fun b : exteriorPlaneBase R => |u b|+
            helicoidGraphGradientNorm (extendOpenScalar u) b.1)
            (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0) := by
  obtain ⟨ε,hε0,hε,hsmall,_⟩ := exists_small_thin_angle_parameter hA (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨K₁,hK₁,hT₁⟩ := hthin ε hε0
  obtain ⟨K₂,hK₂,hT₂⟩ := hcurves ε hε0 hε
  let K := K₀ ∪ (K₁ ∪ K₂)
  have hK : IsCompact K := hK₀.union (hK₁.union hK₂)
  have hn₀ {q} (hq : q ∉ K) : q ∉ K₀ := fun h => hq (Or.inl h)
  have hn₁ {q} (hq : q ∉ K) : q ∉ K₁ := fun h => hq (Or.inr (Or.inl h))
  have hn₂ {q} (hq : q ∉ K) : q ∉ K₂ := fun h => hq (Or.inr (Or.inr h))
  have hTube q (hq : q ∉ K) := (hT₁ q (hn₁ hq)).1
  have hheight q (hq : q ∉ K) := (hT₁ q (hn₁ hq)).2
  obtain ⟨R,hR,hSc,e,he,u,hu,hgraph⟩ := controlled_thin_punctured_curve_smooth_normal_graph p
    hp (hX.mono (fun _ hq => hn₀ hq)) hK c
    (fun q hq => hmem q (hn₀ hq)) (fun q hq => hsm q (hn₀ hq))
    (fun q hq => hD q (hn₀ hq)) hε0 hε hA (hsmall.trans_lt (by norm_num))
    hTube hheight (fun q hq => hT₂ q (hn₂ hq))
  have hs b : |u b| ≤ 1/2 := (hgraph b).1.trans hε
  have hg b := (hgraph b).2
  refine ⟨K,hK,R,hR,hSc,e,he,u,hu,(fun b => ⟨hs b,hg b⟩),?_⟩
  have heval (q : helicoidProjectedEnd X K (exteriorPlaneBase R)) :
      (e q).1 = helicoidBaseCoordinates (X q.1) := by rw [he]; rfl
  have ht : Tendsto u
      (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0) := by
    apply helicoid_graph_height_tendsto_zero hp.continuous (by norm_num : (1/2 : ℝ) < 1) hs hg
    intro δ hδ
    obtain ⟨L,hL,hLt⟩ := hthin (δ/2) (by positivity)
    exact ⟨L,hL,fun q hq => ((hLt q hq).2).trans_lt (by linarith)⟩
  have hgrad := helicoid_global_graph_gradient_tendsto_zero hp.continuous (exteriorPlaneBase_isOpen R)
    e heval hg hu hs c (fun q hq => hmem q (hn₀ hq.1)) (fun q hq => hsm q (hn₀ hq.1))
    (fun q hq => hD q (hn₀ hq.1)) (fun q hq => hTube q hq.1) hA (by
      intro δ hδ hδsmall
      obtain ⟨L,hL,hLt⟩ := hcurves δ hδ hδsmall
      exact ⟨L,hL,fun q _ hq => hLt q hq⟩)
  simpa only [Function.comp_apply,abs_zero,zero_add] using!
    ((continuous_abs.tendsto 0).comp ht).add hgrad

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.controlled_thin_tail_C1_normal_graph
