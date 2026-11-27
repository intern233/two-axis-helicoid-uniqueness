import TwoAxisHelicoid.RemovableCoverMorphism
import Mathlib.Topology.ContinuousMap.Basic

namespace TwoAxisHelicoid
open Filter Set Topology

/-- Two lifts of one base map that agree densely agree everywhere.
The covering map supplies relative separation, so neither total space
nor base needs an independent Hausdorff or regularity assumption. -/
theorem cover_maps_eq_of_dense {A B E : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E]
    {p : E → B} (hp : IsCoveringMap p) {u v : A → E} (hu : Continuous u) (hv : Continuous v)
    (hbase : ∀ a, p (u a) = p (v a)) {D : Set A} (hd : Dense D) (he : EqOn u v D) : u = v := by
  have hc := hp.isSeparatedMap.isClosed_eqLocus hu hv (funext hbase)
  have hsub : D ⊆ {x | u x = v x} := he
  have h := closure_minimal hsub hc
  rw [hd.closure_eq] at h
  exact funext fun x => h (mem_univ x)

/-- Construct the extension by gluing actual local sections, using the
closed relative diagonal of the target covering for overlap uniqueness. -/
theorem dense_cover_lift_glued {A B E : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E]
    {p : E → B} (hp : IsCoveringMap p) {D : Set A} (hd : Dense D)
    (hloc : ∀ a : A, ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ SimplyConnectedSpace V ∧
      LocallyPathConnectedSpace V ∧ IsConnected {v : V | v.1 ∈ D})
    (φ : C(A,B)) (f : C(D,E)) (hf : ∀ a, p (f a) = φ a.1) :
    ∃! H : C(A,E), (∀ x, p (H x) = φ x) ∧ ∀ a : D, H a.1 = f a := by
  classical
  choose V hV hxV hs hl hc using hloc
  have sections (x : A) : ∃ g : C(V x,E), (∀ v, p (g v) = φ v.1) ∧
      ∀ v : V x, ∀ h : v.1 ∈ D, g v = f ⟨v.1,h⟩ := by
    let _ := hs x
    let _ := hl x
    exact covering_map_lift_on_connected_deleted_neighborhood hp (hc x) φ f hf
  choose g hg hD using sections
  have compatibility (x y z : A) (hx : z ∈ V x) (hy : z ∈ V y) : g x ⟨z,hx⟩ = g y ⟨z,hy⟩ := by
    let W := V x ∩ V y
    let l : W → V x := fun w => ⟨w.1,w.2.1⟩
    let r : W → V y := fun w => ⟨w.1,w.2.2⟩
    have eq := cover_maps_eq_of_dense hp ((g x).continuous.comp (continuous_subtype_val.subtype_mk _ : Continuous l))
      ((g y).continuous.comp (continuous_subtype_val.subtype_mk _ : Continuous r))
      (fun w => (hg x (l w)).trans (hg y (r w)).symm)
      (hd.preimage ((hV x).inter (hV y)).isOpenMap_subtype_val)
      (fun w hw => (hD x (l w) hw).trans (hD y (r w) hw).symm)
    exact congrFun eq ⟨z,hx,hy⟩
  have hnb (x : A) : ∃ y, V y ∈ 𝓝 x := ⟨x,(hV x).mem_nhds (hxV x)⟩
  let H := ContinuousMap.liftCover V g compatibility hnb
  have Hval (x : A) : H x = g x ⟨x,hxV x⟩ := ContinuousMap.liftCover_coe (φ := g) (hφ := compatibility) (hS := hnb) ⟨x,hxV x⟩
  have Hbase (x) : p (H x) = φ x := (congrArg p (Hval x)).trans (hg x _)
  have Hdel (x : D) : H x.1 = f x := (Hval _).trans (hD x.1 _ x.2)
  refine ⟨H,⟨Hbase,Hdel⟩,?_⟩
  intro T hT
  apply DFunLike.ext'
  exact cover_maps_eq_of_dense hp T.continuous H.continuous (fun x => (hT.1 x).trans (Hbase x).symm) hd
    (fun x hx => (hT.2 ⟨x,hx⟩).trans (Hdel ⟨x,hx⟩).symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.dense_cover_lift_glued
