import TwoAxisHelicoid.CompactPunctureAxis
import Mathlib.Topology.Maps.Basic

namespace TwoAxisHelicoid
open Set Topology

/-- A complete ambient axis on an embedded once-punctured compact surface
gives a connected intrinsic fixed set, provided the ambient reflection is
already known to act on the surface. -/
theorem embedded_axis_reflection_fixed_locus_connected
    {M V : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M] [TopologicalSpace V]
    {p : M} {X : M → V} (hX : ∀ q ≠ p, ContinuousAt X q)
    (hEmb : IsEmbedding (fun q : {q : M // q ≠ p} => X q.1))
    {axis : ℝ → V} (haxis : Continuous axis)
    {coordinate : V → ℝ} (hcoordinate : Continuous coordinate)
    (hparameter : ∀ r, coordinate (axis r) = r)
    (hcontained : ∀ r, ∃ q : {q : M // q ≠ p}, X q.1 = axis r)
    {R : V → V} (hR : ∀ v, R v = v ↔ v ∈ range axis)
    {f : M → M} (hf : Continuous f) (hfp : f p = p) (hinv : Function.Involutive f)
    (hequiv : ∀ q ≠ p, X (f q) = R (X q)) :
    IsConnected {q : M | f q = q} := by
  classical
  choose γ hγ using hcontained
  have hγcont : Continuous γ := hEmb.continuous_iff.mpr (by
    change Continuous (fun r => X (γ r).1)
    have he : (fun r => X (γ r).1) = axis := funext hγ
    rwa [he])
  have hfpres (q : M) (hq : q ≠ p) : f q ≠ p := by
    intro he
    apply hq
    have h := congrArg f he
    simpa only [hinv q,hfp] using h
  have hfix (r : ℝ) : f (γ r).1 = (γ r).1 := by
    have hr : R (X (γ r).1) = X (γ r).1 := (hR _).mpr ⟨r,(hγ r).symm⟩
    have he := (hequiv (γ r).1 (γ r).2).trans hr
    exact congrArg Subtype.val (hEmb.injective
      (a₁ := ⟨f (γ r).1,hfpres _ (γ r).2⟩) (a₂ := γ r) he)
  apply compact_fixed_locus_connected_of_axis hf
    (u := fun q => coordinate (X q))
    (γ := fun r => (γ r).1)
    (fun q hq => hcoordinate.continuousAt.comp (hX q hq))
    (continuous_subtype_val.comp hγcont)
    (fun r => by rw [hγ,hparameter]) hfix
  intro q hq hfixq
  have hr : R (X q) = X q := by
    have he := hequiv q hq
    rw [hfixq] at he
    exact he.symm
  obtain ⟨r,hr⟩ := (hR (X q)).mp hr
  refine ⟨r,?_⟩
  exact congrArg Subtype.val (hEmb.injective (a₁ := γ r) (a₂ := ⟨q,hq⟩)
    ((hγ r).trans hr))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.embedded_axis_reflection_fixed_locus_connected
