import TwoAxisHelicoid.PunctureInverseChart
import TwoAxisHelicoid.CompactPunctureProperties

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology
set_option maxHeartbeats 1000000

/-- Transport a genuine height chart through the actual quotient chart.
The resulting chart covers every sufficiently far part of the punctured
compact surface, and its inverse is the actual projected height inverse. -/
theorem projected_puncture_height_chart
    {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    {p : M} (hne : Nonempty {q : M // q ≠ p})
    (e : OpenPartialHomeomorph ℂ M) (he0 : (0 : ℂ) ∈ e.source) (he : e 0 = p)
    (heo : IsOpenMap (e : ℂ → M))
    (h : OpenPartialHomeomorph ℂ ℂ)
    (hs : h.source ∈ 𝓝[≠] (0 : ℂ)) (ht : h.target ∈ cobounded ℂ)
    (hH : Tendsto h (𝓝[≠] 0) (cobounded ℂ))
    (hK : Tendsto h.symm (cobounded ℂ) (𝓝[≠] 0)) :
    ∃ E : OpenPartialHomeomorph {q : M // q ≠ p} ℂ,
      (∀ S : ℝ, ∃ K : Set {q : M // q ≠ p}, IsCompact K ∧
        ∀ q ∉ K, q ∈ E.source ∧ S < ‖E q‖) ∧
      (∀ᶠ ξ : ℂ in cobounded ℂ, ξ ∈ E.target ∧ (E.symm ξ).1 = e (h.symm ξ)) := by
  let U : TopologicalSpace.Opens M := ⟨{q | q ≠ p},isOpen_compl_singleton⟩
  let e₀ : OpenPartialHomeomorph {q : M // q ≠ p} ℂ :=
    e.symm.subtypeRestr (s := U) hne
  let E := e₀.trans h
  refine ⟨E,?_,?_⟩
  · intro S
    apply compact_puncture_projected_property heo he
    filter_upwards [nhdsWithin_le_nhds (e.open_source.mem_nhds he0),hs,
      hH.eventually (tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop S))] with z hz hzs hzS
    intro q hq
    have hqs : q.1 ∈ e.target := hq ▸ e.map_source hz
    have hq₀ : q ∈ e₀.source := by
      change (⟨q.1,q.2⟩ : U) ∈ (e.symm.subtypeRestr (s := U) hne).source
      rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact hqs
    have heq : e₀ q = z := by
      change e.symm q.1 = z
      rw [← hq,e.left_inv hz]
    refine ⟨⟨hq₀,?_⟩,?_⟩
    · change e₀ q ∈ h.source
      rwa [heq]
    · change S < ‖h (e₀ q)‖
      rwa [heq]
  · filter_upwards [ht,hK.eventually (nhdsWithin_le_nhds (e.open_source.mem_nhds he0)),
      hK.eventually self_mem_nhdsWithin] with ξ hξ hξs hξn
    have hnp : e (h.symm ξ) ≠ p := by
      intro hh
      exact hξn (e.injOn hξs he0 (hh.trans he.symm))
    let q : U := ⟨e (h.symm ξ),hnp⟩
    have hq : q.1 ∈ e.symm.source := e.map_source hξs
    have htarget : h.symm ξ ∈ e₀.target := by
      have hh := e.symm.map_subtype_source (s := U) hne (x := q) hq
      change e.symm (e (h.symm ξ)) ∈ e₀.target at hh
      rwa [e.left_inv hξs] at hh
    refine ⟨⟨hξ,htarget⟩,?_⟩
    exact e.symm.subtypeRestr_symm_apply (U := U) hne (y := h.symm ξ) htarget

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.projected_puncture_height_chart
