import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded

namespace TwoAxisHelicoid
open MeasureTheory Set Filter
open scoped Topology

/-- Differentiation under a finite interval integral, with continuity on a compact
parameter rectangle providing the domination required by the Bochner theorem. -/
theorem hasDerivAt_intervalIntegral_compact {F F' : ℝ → ℝ → ℂ} {l u x a b : ℝ}
    (hx : x ∈ Ioo l u) (hab : a ≤ b)
    (hc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Icc l u ×ˢ Icc a b))
    (hc' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2) (Icc l u ×ˢ Icc a b))
    (hd : ∀ s ∈ Ioo l u, ∀ y ∈ Icc a b, HasDerivAt (fun r => F r y) (F' s y) s) :
    HasDerivAt (fun r => ∫ y : ℝ in a..b, F r y) (∫ y : ℝ in a..b, F' x y) x := by
  have hsection (s : ℝ) (hs : s ∈ Icc l u) : ContinuousOn (F s) (Icc a b) :=
    hc.comp (f := fun y : ℝ => (s,y)) (by fun_prop) (fun _ hy => ⟨hs,hy⟩)
  have hsection' (s : ℝ) (hs : s ∈ Icc l u) : ContinuousOn (F' s) (Icc a b) :=
    hc'.comp (f := fun y : ℝ => (s,y)) (by fun_prop) (fun _ hy => ⟨hs,hy⟩)
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc'
  have hx' : x ∈ Icc l u := ⟨hx.1.le,hx.2.le⟩
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hmeas : ∀ᶠ s in 𝓝 x, AEStronglyMeasurable (F s) μ := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
    exact (hsection s ⟨hs.1.le,hs.2.le⟩).aestronglyMeasurable measurableSet_Icc
  have hint : Integrable (F x) μ := (hsection x hx').integrableOn_compact isCompact_Icc
  have hmeas' : AEStronglyMeasurable (F' x) μ :=
    (hsection' x hx').aestronglyMeasurable measurableSet_Icc
  have hbound : ∀ᵐ y ∂μ, ∀ s ∈ Ioo l u, ‖F' s y‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    intro s hs
    exact hM (s,y) ⟨⟨hs.1.le,hs.2.le⟩,hy⟩
  have hdiff : ∀ᵐ y ∂μ, ∀ s ∈ Ioo l u, HasDerivAt (fun r => F r y) (F' s y) s := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact fun s hs => hd s hs y hy
  have hmInt : Integrable (fun _ : ℝ => M) μ := by
    change IntegrableOn (fun _ : ℝ => M) (Icc a b) volume
    exact integrableOn_const (ne_of_lt isCompact_Icc.measure_lt_top)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => M) (μ := μ)
    (isOpen_Ioo.mem_nhds hx) hmeas hint hmeas' hbound hmInt hdiff).2
  simpa only [μ, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.hasDerivAt_intervalIntegral_compact
