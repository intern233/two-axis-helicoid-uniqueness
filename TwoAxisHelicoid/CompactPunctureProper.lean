import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace TwoAxisHelicoid
open Set Filter Topology Bornology
open scoped Topology

/-- On a compact parameter space with one deleted point, actual extrinsic
escape at that point implies properness of the punctured spatial map. -/
theorem compact_puncture_map_isProperMap {M : Type*} [TopologicalSpace M]
    [CompactSpace M] [T2Space M] {p : M} {X : M → Fin 3 → ℝ}
    (hX : ∀ q ≠ p, ContinuousAt X q)
    (hescape : Tendsto X (𝓝[≠] p) (cobounded (Fin 3 → ℝ))) :
    IsProperMap (fun q : {q : M // q ≠ p} => X q.1) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨?_,?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro q
    exact (hX q.1 q.2).comp continuous_subtype_val.continuousAt
  · intro K hK
    rw [Subtype.isCompact_iff]
    have he : Subtype.val '' ((fun q : {q : M // q ≠ p} => X q.1) ⁻¹' K) =
        {q : M | q ≠ p ∧ X q ∈ K} := by
      ext q
      constructor
      · rintro ⟨⟨r,hr⟩,hKr,rfl⟩
        exact ⟨hr,hKr⟩
      · rintro ⟨hq,hKq⟩
        exact ⟨⟨q,hq⟩,hKq,rfl⟩
    rw [he]
    apply IsClosed.isCompact
    rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
    intro q hq
    by_cases hqp : q = p
    · subst q
      have hn : ∀ᶠ q in 𝓝[≠] p, X q ∉ K := hescape.eventually hK.isBounded
      simp only [nhdsWithin,eventually_inf_principal] at hn
      filter_upwards [hn] with q hq hmem
      exact hq hmem.1 hmem.2
    · have hnot : X q ∉ K := fun h => hq ⟨hqp,h⟩
      have hn : ∀ᶠ r in 𝓝 q, X r ∉ K :=
        (hX q hqp).eventually (hK.isClosed.isOpen_compl.mem_nhds hnot)
      filter_upwards [hn] with r hr hmem
      exact hr hmem.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_puncture_map_isProperMap
