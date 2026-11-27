import TwoAxisHelicoid.OrderedProperCover
import Mathlib.Topology.Homeomorph.Lemmas

namespace TwoAxisHelicoid
open Set Topology

/-- The lowest sheet of a surjective proper ordered local homeomorphism
is an actual open section, without a connectedness assumption on its
total space. -/
theorem lowest_fiber_open_section {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} {h : E → ℝ} (hp : IsProperMap p) (hl : IsLocalHomeomorph p)
    (hs : Function.Surjective p) (hh : Continuous h)
    (hsep : ∀ a b, p a = p b → h a = h b → a = b) :
    ∃ f : X → E, IsOpenEmbedding f ∧ (∀ x, p (f x) = x) ∧ ∀ x e, p e = x → h (f x) ≤ h e := by
  let U := lowestFiberPoints p h
  have hU : IsOpen U := lowestFiberPoints_isOpen hp hh hl hsep
  let f := fun q : U => p q.1
  have hinj : Function.Injective f := by
    intro a b he
    exact Subtype.ext (hsep _ _ he (le_antisymm (a.2 _ he.symm) (b.2 _ he)))
  have hsur : Function.Surjective f := by
    intro x
    obtain ⟨a,ha⟩ := hs x
    obtain ⟨q,hq,hmin⟩ := (hp.isCompact_preimage (K := {x}) isCompact_singleton).exists_isMinOn
      (show (p ⁻¹' {x}).Nonempty from ⟨a,ha⟩) hh.continuousOn
    have hx : p q = x := hq
    exact ⟨⟨q,fun z hz => hmin (hz.trans hx)⟩,hx⟩
  let e := (Equiv.ofBijective f ⟨hinj,hsur⟩).toHomeomorphOfContinuousOpen
    (hp.continuous.comp continuous_subtype_val) (hl.isOpenMap.comp hU.isOpenEmbedding_subtypeVal.isOpenMap)
  refine ⟨fun x => (e.symm x).1,hU.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding,
    fun x => e.apply_symm_apply x,fun x a ha => ?_⟩
  exact (e.symm x).2 a (ha.trans (e.apply_symm_apply x).symm)

/-- A proper ordered local cover with at least two points in each fiber
contains two disjoint, globally ordered open sheets. -/
theorem ordered_cover_has_two_disjoint_open_sections {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} {h : E → ℝ} (hp : IsProperMap p) (hl : IsLocalHomeomorph p)
    (hh : Continuous h) (hsep : ∀ a b, p a = p b → h a = h b → a = b)
    (hm : ∀ x, ∃ a b, p a = x ∧ p b = x ∧ a ≠ b) :
    ∃ f g : X → E, IsOpenEmbedding f ∧ IsOpenEmbedding g ∧ Disjoint (range f) (range g) := by
  have hs : Function.Surjective p := fun x => by obtain ⟨a,b,ha,_,_⟩ := hm x; exact ⟨a,ha⟩
  obtain ⟨lo,hlo,plo,hmin⟩ := lowest_fiber_open_section hp hl hs hh hsep
  obtain ⟨hi,hhi,phi,hmax⟩ := lowest_fiber_open_section hp hl hs hh.neg
    (fun a b he hh => hsep a b he (neg_injective hh))
  refine ⟨lo,hi,hlo,hhi,Set.disjoint_left.mpr ?_⟩
  rintro _ ⟨x,rfl⟩ ⟨y,he⟩
  have xy : x = y := (plo x).symm.trans ((congrArg p he.symm).trans (phi y))
  subst y
  obtain ⟨a,b,ha,hb,hab⟩ := hm x
  have eq (w : E) (hw : p w = x) : h (lo x) = h w := le_antisymm (hmin x w hw)
    (by simpa only [Pi.neg_apply,neg_le_neg_iff,he] using hmax x w hw)
  exact hab (hsep a b (ha.trans hb.symm) ((eq a ha).symm.trans (eq b hb)))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ordered_cover_has_two_disjoint_open_sections
