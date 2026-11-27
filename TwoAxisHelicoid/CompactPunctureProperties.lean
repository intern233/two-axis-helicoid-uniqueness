import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Complex.Basic

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- A property valid in a punctured local parameter holds outside a
compact core of the actual punctured compact space. The projection is
open; no global chart or global inverse is assumed. -/
theorem compact_puncture_projected_property
    {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    {p : M} {π : ℂ → M} (hπ : IsOpenMap π) (hπ0 : π 0 = p)
    {P : {q : M // q ≠ p} → Prop}
    (hP : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ q : {q : M // q ≠ p}, π z = q.1 → P q) :
    ∃ K : Set {q : M // q ≠ p}, IsCompact K ∧ ∀ q ∉ K, P q := by
  simp only [nhdsWithin,eventually_inf_principal] at hP
  obtain ⟨U,hU,hUo,hU0⟩ := mem_nhds_iff.mp hP
  let V : Set M := π '' U
  have hVo : IsOpen V := hπ U hUo
  have hpV : p ∈ V := ⟨0,hU0,hπ0⟩
  let K : Set {q : M // q ≠ p} := Subtype.val ⁻¹' Vᶜ
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have he : Subtype.val '' K = Vᶜ := by
      ext q
      constructor
      · rintro ⟨q,hq,rfl⟩
        exact hq
      · intro hq
        have hqp : q ≠ p := by
          rintro rfl
          exact hq hpV
        exact ⟨⟨q,hqp⟩,hq,rfl⟩
    rw [he]
    exact hVo.isClosed_compl.isCompact
  refine ⟨K,hK,?_⟩
  intro q hq
  have hqV : q.1 ∈ V := by simpa only [K,mem_preimage,mem_compl_iff,not_not] using hq
  obtain ⟨z,hz,hzq⟩ := hqV
  apply hU hz (show z ≠ 0 from ?_) q hzq
  intro hz0
  exact q.2 (hzq.symm.trans (by simpa only [hz0] using hπ0))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.compact_puncture_projected_property
