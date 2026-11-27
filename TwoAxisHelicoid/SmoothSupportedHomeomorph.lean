import TwoAxisHelicoid.SupportedPartialHomeomorph
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology ContDiff

theorem extendPartialMap_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) {K : Set E} (hK : IsClosed K) (hKU : K ⊆ e.source)
    (hfix : ∀ x ∈ e.source, x ∉ K → e x = x)
    (hsmooth : ∀ x ∈ e.source, ContDiffAt ℝ (∞ : WithTop ℕ∞) e x) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (extendPartialMap e) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ e.source
  · have he : extendPartialMap e =ᶠ[𝓝 x] e := by
      filter_upwards [e.open_source.mem_nhds hx] with y hy
      exact extendPartialMap_of_mem e hy
    exact (hsmooth x hx).congr_of_eventuallyEq he
  · have hn : x ∉ K := fun h => hx (hKU h)
    have he : extendPartialMap e =ᶠ[𝓝 x] id := by
      filter_upwards [hK.isOpen_compl.mem_nhds hn] with y hy
      exact extendPartialMap_fixes e hfix hy
    exact contDiffAt_id.congr_of_eventuallyEq he

theorem extendSupportedHomeomorph_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : OpenPartialHomeomorph E E) (hU : e.source = e.target)
    {K : Set E} (hK : IsClosed K) (hKU : K ⊆ e.source)
    (hfix : ∀ x ∈ e.source, x ∉ K → e x = x)
    (hsmooth : ∀ x ∈ e.source, ContDiffAt ℝ (∞ : WithTop ℕ∞) e x)
    (hinverse : ∀ x ∈ e.target, ContDiffAt ℝ (∞ : WithTop ℕ∞) e.symm x) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (extendSupportedHomeomorph e hU hK hKU hfix) ∧
      ContDiff ℝ (∞ : WithTop ℕ∞) (extendSupportedHomeomorph e hU hK hKU hfix).symm := by
  refine ⟨extendPartialMap_contDiff e hK hKU hfix hsmooth,?_⟩
  apply extendPartialMap_contDiff e.symm hK
  · simpa only [OpenPartialHomeomorph.symm_source,← hU] using hKU
  · intro x hx hn
    have hs : x ∈ e.source := by simpa only [OpenPartialHomeomorph.symm_source,← hU] using hx
    have hi := e.left_inv hs
    rwa [hfix x hs hn] at hi
  · exact hinverse

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.extendSupportedHomeomorph_smooth
