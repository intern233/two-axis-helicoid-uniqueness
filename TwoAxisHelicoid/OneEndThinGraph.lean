import TwoAxisHelicoid.OneEndHelicoidProjection
import TwoAxisHelicoid.ControlledThinTailC1Graph
import TwoAxisHelicoid.UnitCurveThinTails

namespace TwoAxisHelicoid
open Real Set Filter Bornology
open scoped Topology ContDiff

/-- An arbitrary one-ended proper embedded surface with controlled tangent
segments is a single smooth normal graph outside a compact set. -/
private theorem one_end_thin_smooth_graph
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (tail : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K) {X : M → HelicoidTubeCoordinates}
    (hp : IsProperMap X) {K : Set M}
    (hX : InjOn X Kᶜ) (hK : IsCompact K)
    (c : M → OpenPartialHomeomorph M (ℝ × ℝ))
    (hmem : ∀ q ∉ K, q ∈ (c q).source)
    (hsm : ∀ q ∉ K, ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ (c q).symm) (c q q))
    (hD : ∀ q ∉ K, Function.Injective (fderiv ℝ (X ∘ (c q).symm) (c q q)))
    {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1/2) (hA : 0 ≤ A)
    (hsmall : (3+A/2)*sqrt ε < 1)
    (hTube : ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target)
    (hheight : ∀ q ∉ K, |helicoidSignedDistance (X q)| ≤ ε)
    (hcurves : ∀ q ∉ K, HasControlledUnitTangentCurves (X q)
      (fderiv ℝ (X ∘ (c q).symm) (c q q)) ε A) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (helicoidProjectedEnd X K (exteriorPlaneBase R))ᶜ ∧
      ∃ e : helicoidProjectedEnd X K (exteriorPlaneBase R) ≃ₜ exteriorPlaneBase R,
        (e : helicoidProjectedEnd X K (exteriorPlaneBase R) → exteriorPlaneBase R) =
          helicoidEndProjection X K (exteriorPlaneBase R) ∧
        ∃ u : exteriorPlaneBase R → ℝ,
          ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R) ∧
          ∀ b, |u b| ≤ ε ∧ X (e.symm b).1 = helicoidTubeMap ((u b,b.1.1),b.1.2) := by
  have hl := thin_charts_projection_isLocalHomeomorphOn (S := Kᶜ) c hmem hsm hTube hD
    hε0 hε hA hsmall hcurves
  obtain ⟨R,hR,hSc,e,he,u,_hu,hgraph⟩ := helicoid_one_end_exterior_graph tail
    hp hX hK (hε.trans_lt (by norm_num)) hTube hheight hl
  refine ⟨R,hR,hSc,e,he,u,?_,hgraph⟩
  have heval (q : helicoidProjectedEnd X K (exteriorPlaneBase R)) :
      (e q).1 = helicoidBaseCoordinates (X q.1) := by rw [he]; rfl
  have huval (b : exteriorPlaneBase R) :
      u b = helicoidSignedDistance (X (e.symm b).1) := by
    rw [(hgraph b).2]
    exact (helicoidSignedDistance_on_normal
      (show ((u b,b.1.1),b.1.2) ∈ helicoidTubeStrip from
        (hgraph b).1.trans_lt (hε.trans_lt (by norm_num)))).symm
  apply contDiffOn_extendOpenScalar_of_smooth_germs (exteriorPlaneBase_isOpen R)
  apply helicoid_graph_height_has_smooth_germs e heval huval
    (fun q => hTube q.1 q.2.1)
  intro q
  obtain ⟨φ,hφ,hmap,hXs⟩ := thin_chart_projection_local_inverse (c q.1) (hmem q.1 q.2.1)
    (hsm q.1 q.2.1) (hTube q.1 q.2.1) (hD q.1 q.2.1) hε0 hε hA hsmall (hcurves q.1 q.2.1)
  exact ⟨φ,hφ,hmap,by simpa only [heval] using hXs⟩

/-- The global graph and gradient decay use only the one-end hypothesis on the
source topology. Its compactification need not be a surface. -/
theorem one_end_thin_C1_graph
    {M : Type*} [TopologicalSpace M] [T2Space M]
    (tail : ∀ K : Set M, IsCompact K → ∃ U : Set M, IsConnected U ∧ IsCompact Uᶜ ∧ Disjoint U K) {X : M → HelicoidTubeCoordinates}
    (hp : IsProperMap X) {K₀ : Set M}
    (hX : InjOn X K₀ᶜ) (hK₀ : IsCompact K₀)
    (c : M → OpenPartialHomeomorph M (ℝ × ℝ))
    (hmem : ∀ q ∉ K₀, q ∈ (c q).source)
    (hsm : ∀ q ∉ K₀, ContDiffAt ℝ (∞ : WithTop ℕ∞) (X ∘ (c q).symm) (c q q))
    (hD : ∀ q ∉ K₀, Function.Injective (fderiv ℝ (X ∘ (c q).symm) (c q q)))
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ K : Set M, IsCompact K ∧
      ∀ q ∉ K, X q ∈ helicoidTubeEquiv.target ∧ |helicoidSignedDistance (X q)| ≤ ε)
    {A : ℝ} (hA : 0 ≤ A)
    (hcurves : ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ∃ K : Set M, IsCompact K ∧
      ∀ q ∉ K, HasControlledUnitTangentCurves (X q)
        (fderiv ℝ (X ∘ (c q).symm) (c q q)) ε A) :
    ∃ K : Set M, IsCompact K ∧ ∃ R : ℝ, 0 < R ∧
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
  obtain ⟨R,hR,hSc,e,he,u,hu,hgraph⟩ := one_end_thin_smooth_graph tail
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
#print axioms TwoAxisHelicoid.one_end_thin_C1_graph
