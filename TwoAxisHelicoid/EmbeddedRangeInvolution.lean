import Mathlib.Topology.Homeomorph.Lemmas

namespace TwoAxisHelicoid
open Set Topology

/-- The actual action on an embedded surface is forced by a continuous
ambient involution preserving its image. -/
noncomputable def embeddedRangeInvolution {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    {X : M → E} (hX : IsEmbedding X) (S : E → E) (hS : Continuous S)
    (hi : Function.Involutive S) (hin : ∀ p, S (X p) ∈ range X) : M ≃ₜ M := by
  let f (p : M) := hX.toHomeomorph.symm ⟨S (X p),hin p⟩
  have he (p : M) : X (f p) = S (X p) :=
    congrArg Subtype.val (hX.toHomeomorph.apply_symm_apply ⟨S (X p),hin p⟩)
  have hfi : Function.Involutive f := fun p => hX.injective (by rw [he,he,hi])
  have hc : Continuous f := hX.toHomeomorph.symm.continuous.comp ((hS.comp hX.continuous).subtype_mk hin)
  exact ⟨⟨f,f,hfi,hfi⟩,hc,hc⟩

theorem embeddedRangeInvolution_eq {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
    {X : M → E} (hX : IsEmbedding X) (S : E → E) (hS : Continuous S)
    (hi : Function.Involutive S) (hin : ∀ p, S (X p) ∈ range X) (p : M) :
    X (embeddedRangeInvolution hX S hS hi hin p) = S (X p) :=
  congrArg Subtype.val (hX.toHomeomorph.apply_symm_apply ⟨S (X p),hin p⟩)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embeddedRangeInvolution_eq
