module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Separation.Hausdorff

public section
namespace TwoAxisHelicoid
open Set Topology

/-- A compact simply connected parameter set embedded in the base of a
cover lifts into one open sheet surrounding its entire image. -/
theorem compact_embedding_lifts_into_open_sheet {A E X : Type*}
    [TopologicalSpace A] [CompactSpace A] [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    [TopologicalSpace E] [T2Space E] [TopologicalSpace X] [T2Space X]
    {p : E → X} (cover : IsCoveringMap p) (u : C(A,X)) (emb : IsEmbedding u)
    (a₀ : A) (e₀ : E) (start : p e₀=u a₀) :
    ∃ (F : C(A,E)) (V : Set E), F a₀=e₀ ∧ (∀ a, p (F a)=u a) ∧
      IsEmbedding F ∧ IsOpen V ∧ range F⊆V ∧ IsOpenEmbedding (V.domRestrict p) := by
  obtain ⟨F,⟨base,eq⟩,_⟩ := cover.existsUnique_continuousMap_lifts u a₀ e₀ start
  have lift (a : A) : p (F a)=u a := congrFun eq a
  have inj : Function.Injective F := fun x y h => emb.injective ((lift x).symm.trans ((congrArg p h).trans (lift y)))
  have one : InjOn p (range F) := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ h
    exact congrArg F (emb.injective ((lift x).symm.trans (h.trans (lift y))))
  have loc := cover.isLocalHomeomorph
  obtain ⟨V,op,inside,ij⟩ := one.exists_isOpen_superset (isCompact_range F.continuous)
    (fun _ _ => loc.continuous.continuousAt) (fun x _ => isLocallyInjective_iff_nhds.mp loc.isLocallyInjective x)
  have restrictOpen : IsOpenEmbedding (V.domRestrict p) :=
    (loc.comp op.isOpenEmbedding_subtypeVal.isLocalHomeomorph).isOpenEmbedding_of_injective
      (injOn_iff_injective.mp ij)
  exact ⟨F,V,base,lift,(F.continuous.isClosedEmbedding inj).isEmbedding,op,inside,restrictOpen⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_embedding_lifts_into_open_sheet
