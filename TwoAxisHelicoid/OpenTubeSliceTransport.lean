module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

public section

namespace TwoAxisHelicoid
open Set Topology

/-- Pulling an embedded physical surface back through an open tube
chart gives an open patch of the original surface, with its actual
position unchanged after pushing forward. -/
theorem open_tube_slice_embeds_in_surface {B E M : Type*}
    [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace M]
    (e : OpenPartialHomeomorph B E) (j : M → E) (emb : IsEmbedding j) :
    let A := {b : B | b∈e.source ∧ e b∈range j}
    ∃ g : A → M, IsOpenEmbedding g ∧ ∀ a, j (g a)=e a.1 := by
  intro A
  let D := j ⁻¹' e.target
  let f (x : D) : A := ⟨e.symm (j x.1),e.map_target x.2,
    (e.right_inv x.2).symm ▸ mem_range_self x.1⟩
  let back (a : A) := emb.toHomeomorph.symm ⟨e a.1,a.2.2⟩
  have represented (a : A) : j (back a)=e a.1 := congrArg Subtype.val (emb.toHomeomorph.apply_symm_apply ⟨e a.1,a.2.2⟩)
  let g (a : A) : D := ⟨back a,by
    change j (back a)∈e.target
    rw [represented a]
    exact e.map_source a.2.1⟩
  have cf : Continuous f := (e.continuousOn_symm.comp_continuous
    (emb.continuous.comp continuous_subtype_val) (fun x : D => x.2)).subtype_mk _
  have ce : Continuous (fun a : A => e a.1) := e.continuousOn.comp_continuous continuous_subtype_val (fun a : A => a.2.1)
  have cg : Continuous g := (emb.toHomeomorph.symm.continuous.comp (ce.subtype_mk _)).subtype_mk _
  let H : A ≃ₜ D := {
    toFun := g
    invFun := f
    left_inv := fun a => Subtype.ext (by
      change e.symm (j (back a))=a.1
      rw [represented,e.left_inv a.2.1])
    right_inv := fun x => Subtype.ext (emb.injective (by
      change j (back (f x))=j x.1
      rw [represented]
      exact e.right_inv x.2))
    continuous_toFun := cg
    continuous_invFun := cf }
  have opened : IsOpen D := e.open_target.preimage emb.continuous
  exact ⟨Subtype.val ∘ H,opened.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding,represented⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.open_tube_slice_embeds_in_surface
