import TwoAxisHelicoid.RemovableCoverGluing
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.LocallyPathConnected

namespace TwoAxisHelicoid
open Set Topology

/-- A deleted set has a neighborhood basis on which a covering and its
restriction have the same possible sections. -/
def HasRemovableCoverBasis {X : Type*} [TopologicalSpace X] (D : Set X) : Prop :=
  ∀ x : X, ∀ U : Set X, IsOpen U → x ∈ U →
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ SimplyConnectedSpace V ∧
      LocallyPathConnectedSpace V ∧ IsConnected {v : V | v.1 ∈ D}

variable {X E F : Type*} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace F]

theorem HasRemovableCoverBasis.dense {D : Set X} (hD : HasRemovableCoverBasis D) : Dense D := by
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨x,hx⟩
  obtain ⟨V,_,_,hVU,_,_,hv⟩ := hD x U hU hx
  obtain ⟨y,hy⟩ := hv.nonempty
  exact ⟨y.1,hVU y.2,hy⟩

/-- The local deletion property lifts through every covering chart; this
permits completely arbitrary source and target coverings. -/
theorem HasRemovableCoverBasis.preimage {D : Set X} (hD : HasRemovableCoverBasis D)
    {p : E → X} (hp : IsLocalHomeomorph p) : HasRemovableCoverBasis (p ⁻¹' D) := by
  intro x U hU hx
  obtain ⟨e,hxe,hep⟩ := hp x
  let W := e '' (U ∩ e.source)
  have hW : IsOpen W := e.isOpen_image_of_subset_source (hU.inter e.open_source) inter_subset_right
  have hpW : p x ∈ W := ⟨x,⟨hx,hxe⟩,(congrFun hep x).symm⟩
  obtain ⟨A,hA,hpx,hAW,hs,hl,hc⟩ := hD (p x) W hW hpW
  let _ := hs
  let _ := hl
  have hT : A ⊆ e.target := fun a ha => by
    obtain ⟨z,hz,hza⟩ := hAW ha
    exact hza ▸ e.map_source hz.2
  let V := e.symm '' A
  have hV : IsOpen V := e.isOpen_image_symm_of_subset_target hA hT
  have hxV : x ∈ V := ⟨e x,congrFun hep x ▸ hpx,e.left_inv hxe⟩
  have hVU : V ⊆ U := by
    rintro v ⟨a,ha,rfl⟩
    obtain ⟨z,hz,heq⟩ := hAW ha
    rw [← heq,e.left_inv hz.2]
    exact hz.1
  let H : A ≃ₜ V := e.symm.homeomorphOfImageSubsetSource hT rfl
  have hHp (y : A) : p (H y).1 = y.1 := by
    change p (e.symm y.1) = y.1
    rw [hep,e.right_inv (hT y.2)]
  have hdel : H '' {a : A | a.1 ∈ D} = {v : V | v.1 ∈ p ⁻¹' D} := by
    ext v
    constructor
    · rintro ⟨a,ha,rfl⟩
      change p (H a).1 ∈ D
      rwa [hHp]
    · intro hv
      refine ⟨H.symm v,?_,H.apply_symm_apply v⟩
      change (H.symm v).1 ∈ D
      rw [← hHp,H.apply_symm_apply]
      exact hv
  refine ⟨V,hV,hxV,hVU,H.symm.toHomotopyEquiv.simplyConnectedSpace,
    H.isQuotientMap.locallyPathConnectedSpace,?_⟩
  rw [← hdel]
  exact hc.image H H.continuous.continuousOn

theorem HasRemovableCoverBasis.extends_map {D : Set X}
    (hD : HasRemovableCoverBasis D) {p : E → X} {q : F → X}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : C({e : E // p e ∈ D},F)) (hf : ∀ e, q (f e) = p e.1) :
    ∃! H : C(E,F), (∀ e, q (H e) = p e) ∧ ∀ e : {e : E // p e ∈ D}, H e.1 = f e := by
  have h := hD.preimage hp.isLocalHomeomorph
  refine dense_cover_lift_glued hq h.dense (fun x => ?_) ⟨p,hp.continuous⟩ f hf
  obtain ⟨V,hV,hx,_,hs,hl,hc⟩ := h x univ isOpen_univ (mem_univ _)
  exact ⟨V,hV,hx,hs,hl,hc⟩

/-- Restriction to a removable deletion is fully faithful on covering
isomorphisms. Both compact extensions may be arbitrary coverings. -/
theorem HasRemovableCoverBasis.extends_isomorphism
    {D : Set X} (hD : HasRemovableCoverBasis D) {p : E → X} {q : F → X}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : {e : E // p e ∈ D} ≃ₜ {e : F // q e ∈ D}) (hf : ∀ e, q (f e).1 = p e.1) :
    ∃! H : E ≃ₜ F, (∀ e, q (H e) = p e) ∧ ∀ e : {e : E // p e ∈ D}, H e.1 = (f e).1 := by
  let u₀ : C({e : E // p e ∈ D},F) := ⟨fun e => (f e).1,continuous_subtype_val.comp f.continuous⟩
  let v₀ : C({y : F // q y ∈ D},E) := ⟨fun y => (f.symm y).1,continuous_subtype_val.comp f.symm.continuous⟩
  obtain ⟨u,⟨hu,huK⟩,huniq⟩ := hD.extends_map hp hq u₀ hf
  have hfi (y) : p (f.symm y).1 = q y.1 := (hf (f.symm y)).symm.trans (congrArg (fun z => q z.1) (f.apply_symm_apply y))
  obtain ⟨v,⟨hv,hvK⟩,_⟩ := hD.extends_map hq hp v₀ hfi
  have hleft : (v ∘ u : E → E) = id := by
    apply cover_maps_eq_of_dense hp (v.continuous.comp u.continuous) continuous_id
      (fun x => (hv (u x)).trans (hu x)) (hD.preimage hp.isLocalHomeomorph).dense
    intro x hx
    let e := (⟨x,hx⟩ : {e : E // p e ∈ D})
    change v (u e.1) = e.1
    rw [huK e]
    exact (hvK (f e)).trans (congrArg Subtype.val (f.symm_apply_apply e))
  have hright : (u ∘ v : F → F) = id := by
    apply cover_maps_eq_of_dense hq (u.continuous.comp v.continuous) continuous_id
      (fun x => (hu (v x)).trans (hv x)) (hD.preimage hq.isLocalHomeomorph).dense
    intro y hy
    let e := (⟨y,hy⟩ : {e : F // q e ∈ D})
    change u (v e.1) = e.1
    rw [hvK e]
    exact (huK (f.symm e)).trans (congrArg Subtype.val (f.apply_symm_apply e))
  let H : E ≃ₜ F := ⟨⟨u,v,congrFun hleft,congrFun hright⟩,u.continuous,v.continuous⟩
  refine ⟨H,⟨hu,huK⟩,?_⟩
  intro T hT
  have hh := huniq ⟨T,T.continuous⟩ hT
  exact Homeomorph.ext fun x => DFunLike.congr_fun hh x

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasRemovableCoverBasis.extends_isomorphism
