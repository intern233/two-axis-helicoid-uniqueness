import TwoAxisHelicoid.AffineAmbientFlow
import Mathlib.Topology.Homeomorph.Lemmas

namespace TwoAxisHelicoid
open Set Topology

variable {M E : Type*} [TopologicalSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A complete affine flow preserving the embedded image restricts to a
continuous pointwise family of homeomorphisms of the original parameter
space. The group action and its parameter origin are actual equalities. -/
theorem embedded_ambient_flow_action {X : M → E} (hX : IsEmbedding X) (L : E →L[ℝ] E) (a : E)
    (hin : ∀ t q, affineAmbientFlow L a t (X q) ∈ range X) :
    ∃ f : ℝ → M ≃ₜ M, (∀ t q, X (f t q) = affineAmbientFlow L a t (X q)) ∧
      (∀ q, Continuous (fun t => f t q)) ∧ (∀ s t q, f (s+t) q = f s (f t q)) ∧
      (∀ q, f 0 q = q) ∧ (∀ t q, (f t).symm q = f (-t) q) := by
  let F := affineAmbientFlow L a
  let g := fun t q => hX.toHomeomorph.symm ⟨F t (X q),hin t q⟩
  have he (t : ℝ) (q : M) : X (g t q) = F t (X q) :=
    congrArg Subtype.val (hX.toHomeomorph.apply_symm_apply ⟨F t (X q),hin t q⟩)
  have hg (s t : ℝ) (q : M) : g (s+t) q = g s (g t q) := by
    apply hX.injective
    rw [he,he,he]
    exact affineAmbientFlow_add L a (X q) s t
  have h0 (q : M) : g 0 q = q := hX.injective ((he 0 q).trans (affineAmbientFlow_zero L a _))
  have hcont (t : ℝ) : Continuous (g t) := by
    apply hX.toHomeomorph.symm.continuous.comp
    apply Continuous.subtype_mk
    exact (continuous_iff_continuousAt.mpr fun p => (affineAmbientFlow_hasFDerivAt L a p t).continuousAt).comp hX.continuous
  have ht (q : M) : Continuous (fun t => g t q) := by
    apply hX.toHomeomorph.symm.continuous.comp
    apply Continuous.subtype_mk
    exact continuous_iff_continuousAt.mpr fun t => (affineAmbientFlow_deriv L a (X q) t).continuousAt
  let f (t : ℝ) : M ≃ₜ M := {
    toFun := g t
    invFun := g (-t)
    left_inv := fun q => by rw [← hg,neg_add_cancel,h0]
    right_inv := fun q => by rw [← hg,add_neg_cancel,h0]
    continuous_toFun := hcont t
    continuous_invFun := hcont (-t) }
  exact ⟨f,he,ht,hg,h0,fun _ _ => rfl⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_ambient_flow_action
