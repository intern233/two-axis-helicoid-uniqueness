import TwoAxisHelicoid.StraightAxisComplexParameter
import TwoAxisHelicoid.AxisReflectionGerm
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace TwoAxisHelicoid
open Complex Set Metric Filter InnerProductSpace
open scoped Topology ComplexConjugate

/-- Inverting the actual straightening coordinate and applying harmonic
reflection produces a second point of the same chart for each nearby
spatial half-turn. -/
theorem straightened_harmonic_surface_local_half_turn {X : ℂ → Fin 3 → ℝ}
    {W : ℂ → ℂ} {σ : ℝ → ℂ} {R : ℝ} (hR : 0 < R)
    (hh : ∀ j, HarmonicOnNhd (fun z => X z j) (ball (σ 0) R))
    (hW : AnalyticAt ℂ W (σ 0)) (h0 : W (σ 0) = 0) (hne : deriv W (σ 0) ≠ 0)
    (hXW : ∀ z ∈ ball (σ 0) R, (W z).re = X z 0)
    (hσ : ContinuousAt σ 0) (haxis : ∀ᶠ (s:ℝ) in 𝓝 0, W (σ s) = (s:ℂ) ∧ X (σ s) = ![s,0,0]) :
    ∃ S : ℂ → ℂ, AnalyticAt ℂ S (conj (σ 0)) ∧ S (conj (σ 0)) = σ 0 ∧
      ∀ᶠ z in 𝓝 (σ 0), S (conj z) ∈ ball (σ 0) R ∧ X (S (conj z)) = halfTurnX (X z) := by
  let G := hW.hasStrictDerivAt.localInverse _ _ _ hne
  have hl : ∀ᶠ z in 𝓝 (σ 0), G (W z) = z := hW.hasStrictDerivAt.eventually_left_inverse hne
  have hG : AnalyticAt ℂ G 0 := h0 ▸ hW.analyticAt_localInverse hne
  have hG0 : G 0 = σ 0 := h0 ▸ hl.self_of_nhds
  have hr : ∀ᶠ z in 𝓝 (0:ℂ), W (G z) = z := h0 ▸ hW.hasStrictDerivAt.eventually_right_inverse hne
  have hGB : ∀ᶠ z in 𝓝 (0:ℂ), G z ∈ ball (σ 0) R :=
    hG.continuousAt.eventually (by rw [hG0]; exact ball_mem_nhds _ hR)
  let Y := X ∘ G
  have hY (j : Fin 3) : HarmonicAt (fun w => Y w j) 0 := by
    obtain ⟨F,hF,he⟩ := (hh j).exists_analyticOnNhd_ball_re_eq
    have hFa : AnalyticAt ℂ F (G 0) := hF _ (hG0.symm ▸ mem_ball_self hR)
    apply (harmonicAt_congr_nhds (f₂ := reCLM ∘ (F ∘ G)) ?_).mpr
    · exact (hFa.comp hG).harmonicAt.comp_CLM reCLM
    · filter_upwards [hGB] with w hw
      exact (he hw).symm
  have hx : ∀ᶠ w in 𝓝 (0:ℂ), Y w 0 = w.re := by
    filter_upwards [hGB,hr] with w hw he
    exact (hXW _ hw).symm.trans (congrArg Complex.re he)
  have ha : ∀ᶠ (s:ℝ) in 𝓝 0, Y (s:ℂ) = ![s,0,0] := by
    filter_upwards [haxis,hσ.eventually hl] with s hs hls
    change X (G (s:ℂ)) = _
    rw [← hs.1,hls,hs.2]
  have hSR := harmonic_axis_germ_reflects hY hx ha
  have hWt : Tendsto W (𝓝 (σ 0)) (𝓝 0) := h0 ▸ hW.continuousAt.tendsto
  have hct : Tendsto (fun z => conj (W z)) (𝓝 (σ 0)) (𝓝 0) := by
    simpa [Function.comp_def] using (continuous_conj.continuousAt (x := 0)).tendsto.comp hWt
  let K := fun z => conj (W (conj z))
  have he : K (conj (σ 0)) = 0 := by simp [K,h0]
  have hKK : AnalyticAt ℂ K (conj (σ 0)) := by
    have hc (x : ℂ) (hx : AnalyticAt ℂ W (conj x)) : DifferentiableAt ℂ K x :=
      (complex_reflected_hasDerivAt hx.differentiableAt.hasDerivAt).differentiableAt
    have hnear : ∀ᶠ w in 𝓝 (conj (σ 0)), AnalyticAt ℂ W (conj w) :=
      continuous_conj.continuousAt.eventually
        (show ∀ᶠ z in 𝓝 (conj (conj (σ 0))), AnalyticAt ℂ W z by
          rw [starRingEnd_self_apply]
          exact (isOpen_analyticAt ℂ W).mem_nhds hW)
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · exact (hnear.mono hc).filter_mono nhdsWithin_le_nhds
    · exact (hc _ (by simpa using hW)).continuousAt
  refine ⟨G ∘ K,(show AnalyticAt ℂ G (K (conj (σ 0))) by rw [he]; exact hG).comp hKK,
    by change G (K (conj (σ 0))) = _; rw [he,hG0],?_⟩
  filter_upwards [hWt.eventually hSR,hl,hct.eventually hGB] with z hs hzl hzB
  change X (G (conj (W z))) = halfTurnX (X (G (W z))) at hs
  simpa only [Function.comp_apply,K,starRingEnd_self_apply,hzl] using And.intro hzB hs

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.straightened_harmonic_surface_local_half_turn
