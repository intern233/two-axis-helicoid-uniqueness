import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Homeomorph.Defs

namespace TwoAxisHelicoid
open Topology

theorem punctured_embedding_injective {M V : Type*} [TopologicalSpace M] [TopologicalSpace V]
    {p : M} {X : M → V} (hX : IsEmbedding (fun q : {q : M // q ≠ p} => X q.1))
    {q r : M} (hq : q ≠ p) (hr : r ≠ p) (he : X q = X r) : q = r :=
  congrArg Subtype.val (hX.injective (a₁ := ⟨q,hq⟩) (a₂ := ⟨r,hr⟩) he)

theorem homeomorph_puncture_ne {M : Type*} [TopologicalSpace M] (f : M ≃ₜ M)
    {p : M} (hp : f p = p) {q : M} (hq : q ≠ p) : f q ≠ p := by
  intro he
  apply hq
  apply f.injective
  exact he.trans hp.symm

theorem embedded_equivariant_involution {M V : Type*} [TopologicalSpace M] [TopologicalSpace V]
    {p : M} {X : M → V} (hX : IsEmbedding (fun q : {q : M // q ≠ p} => X q.1))
    (f : M ≃ₜ M) (hfp : f p = p) {R : V → V} (hR : Function.Involutive R)
    (hf : ∀ q ≠ p, X (f q) = R (X q)) : Function.Involutive f := by
  intro q
  by_cases hq : q = p
  · simp [hq,hfp]
  · have hqf := homeomorph_puncture_ne f hfp hq
    apply punctured_embedding_injective hX (homeomorph_puncture_ne f hfp hqf) hq
    rw [hf _ hqf,hf _ hq,hR]

theorem embedded_equivariant_commute {M V : Type*} [TopologicalSpace M] [TopologicalSpace V]
    {p : M} {X : M → V} (hX : IsEmbedding (fun q : {q : M // q ≠ p} => X q.1))
    (f g : M ≃ₜ M) (hfp : f p = p) (hgp : g p = p)
    {R S : V → V} (hRS : Function.Commute R S)
    (hf : ∀ q ≠ p, X (f q) = R (X q)) (hg : ∀ q ≠ p, X (g q) = S (X q)) :
    Function.Commute f g := by
  intro q
  by_cases hq : q = p
  · simp [hq,hfp,hgp]
  · have hqf := homeomorph_puncture_ne f hfp hq
    have hqg := homeomorph_puncture_ne g hgp hq
    apply punctured_embedding_injective hX
      (homeomorph_puncture_ne f hfp hqg) (homeomorph_puncture_ne g hgp hqf)
    rw [hf _ hqg,hg _ hq,hg _ hqf,hf _ hq,hRS]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_equivariant_commute
