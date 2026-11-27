import TwoAxisHelicoid.ControlledThinTailC1Graph
import TwoAxisHelicoid.AnalyticEndControlledCurves
import TwoAxisHelicoid.HolomorphicHeightChart

namespace TwoAxisHelicoid
open Complex Real Set Filter Bornology
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- An actual analytic height chart on a thin, embedded subend gives the
complete C¹ normal-graph conclusion. Only injectivity beyond one compact
core is needed; the rest of the surface need not be embedded. Tangent curves, acceleration bounds, smoothness,
local invertibility and the one-sheet conclusion are all derived. The
thinness and the existence of the end chart remain explicit hypotheses. -/
theorem analytic_embedded_height_end_C1_normal_graph
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M] [T2Space M]
    (p : M) {X : {q : M // q ≠ p} → Fin 3 → ℝ}
    (hp : IsProperMap X) {Kᵢ : Set {q : M // q ≠ p}}
    (hKᵢ : IsCompact Kᵢ) (hXinj : InjOn X Kᵢᶜ)
    (e : OpenPartialHomeomorph {q : M // q ≠ p} ℂ)
    (htail : ∀ S : ℝ, ∃ K : Set {q : M // q ≠ p}, IsCompact K ∧
      ∀ q ∉ K, q ∈ e.source ∧ S < ‖e q‖)
    {f : ℂ → ℂ} (α R₀ : ℝ) (hf : AnalyticAt ℂ f 0)
    (hX : ∀ z : ℂ, R₀ < ‖z‖ → HasFDerivAt (X ∘ e.symm)
      (nullRealDerivative (weierstrassTriple (exp (I*(α : ℂ)*z+infinityCorrection f z)) 1)) z)
    (hthin : ∀ ε : ℝ, 0 < ε → ∃ S : ℝ, ∀ z : ℂ, S < ‖z‖ →
      coordinateToTube (X (e.symm z)) ∈ helicoidTubeEquiv.target ∧
      |helicoidSignedDistance (coordinateToTube (X (e.symm z)))| ≤ ε) :
    ∃ K : Set {q : M // q ≠ p}, IsCompact K ∧ ∃ R : ℝ, 0 < R ∧
      IsCompact (helicoidProjectedEnd (coordinateToTube ∘ X) K (exteriorPlaneBase R))ᶜ ∧
      ∃ E : helicoidProjectedEnd (coordinateToTube ∘ X) K (exteriorPlaneBase R) ≃ₜ exteriorPlaneBase R,
        (E : helicoidProjectedEnd (coordinateToTube ∘ X) K (exteriorPlaneBase R) → exteriorPlaneBase R) =
          helicoidEndProjection (coordinateToTube ∘ X) K (exteriorPlaneBase R) ∧
        ∃ u : exteriorPlaneBase R → ℝ,
          ContDiffOn ℝ (∞ : WithTop ℕ∞) (extendOpenScalar u) (exteriorPlaneBase R) ∧
          (∀ b, |u b| ≤ 1/2 ∧ coordinateToTube (X (E.symm b).1) =
            helicoidTubeMap ((u b,b.1.1),b.1.2)) ∧
          Tendsto (fun b : exteriorPlaneBase R => |u b|+
            helicoidGraphGradientNorm (extendOpenScalar u) b.1)
            (comap (Subtype.val : exteriorPlaneBase R → ℝ × ℝ) (cobounded (ℝ × ℝ))) (𝓝 0) := by
  obtain ⟨B,hBbase,_hB0,hcontrol,_⟩ := analytic_helicoidal_end_unit_geodesics α R₀ hf
  obtain ⟨Kᵣ,hKᵣ,hKᵣtail⟩ := htail B
  let K₀ := Kᵢ ∪ Kᵣ
  have hK₀ : IsCompact K₀ := hKᵢ.union hKᵣ
  have hK₀tail q (hq : q ∉ K₀) := hKᵣtail q (fun h => hq (Or.inr h))
  have hinj : InjOn (coordinateToTube ∘ X) K₀ᶜ := by
    intro q hq w hw he
    exact hXinj (fun h => hq (Or.inl h)) (fun h => hw (Or.inl h)) (coordinateToTube_injective he)
  have hd z (hz : B < ‖z‖) := hX z (hBbase.trans hz)
  have hreg q (hq : q ∉ K₀) := holomorphic_height_chart_regular e
    (fun z hz => (hcontrol z hz).1) hd (hK₀tail q hq).2
  apply controlled_thin_tail_C1_normal_graph p (coordinateToTube_isProperMap hp)
    hinj hK₀ (fun _ => complexChartAsReal e)
    (fun q hq => (hK₀tail q hq).1) (fun q hq => (hreg q hq).1)
    (fun q hq => (hreg q hq).2)
  · intro ε hε
    obtain ⟨S,hS⟩ := hthin ε hε
    obtain ⟨K,hK,hKt⟩ := htail S
    refine ⟨K,hK,?_⟩
    intro q hq
    simpa only [Function.comp_apply,e.left_inv (hKt q hq).1] using hS (e q) (hKt q hq).2
  · exact (by positivity : (0 : ℝ) ≤ |α|+1)
  · intro ε hε0 hε
    obtain ⟨T,_hT,hTcurves⟩ := analytic_helicoidal_thin_end_controlled_curves α R₀ hf hX hthin ε hε0 hε
    obtain ⟨K,hK,hKt⟩ := htail (max T B)
    refine ⟨K,hK,?_⟩
    intro q hq
    have hqT : T < ‖e q‖ := (le_max_left _ _).trans_lt (hKt q hq).2
    have hqB : B < ‖e q‖ := (le_max_right _ _).trans_lt (hKt q hq).2
    rw [(complex_chart_real_differential e (hd (e q) hqB)).fderiv]
    simpa only [Function.comp_apply,e.left_inv (hKt q hq).1] using
      (hTcurves (e q) hqT).precomp Complex.equivRealProdCLM.symm.toContinuousLinearMap

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.analytic_embedded_height_end_C1_normal_graph
