import Mathlib.Topology.Homotopy.Lifting

namespace TwoAxisHelicoid
open Set Topology

/-- The strong retraction data used to compare coverings on a punctured
surface with their restrictions to an unchanged compact core. -/
structure CoverCoreRetraction {B : Type*} [TopologicalSpace B] (K : Set B) where
  flow : C(unitInterval × B,B)
  initial : ∀ b, flow (0,b) = b
  terminal : ∀ b, flow (1,b) ∈ K
  fixed : ∀ t b, b ∈ K → flow (t,b) = b

variable {B E F : Type*} [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace F]
    {K : Set B} (R : CoverCoreRetraction K) {p : E → B} {q : F → B}

theorem CoverCoreRetraction.lift (hp : IsCoveringMap p) :
    ∃ A : C(unitInterval × E,E), (∀ e, A (0,e) = e) ∧
      (∀ t e, p (A (t,e)) = R.flow (t,p e)) ∧ ∀ t e, p e ∈ K → A (t,e) = e := by
  let H : C(unitInterval × E,B) := ⟨fun u => R.flow (u.1,p u.2),
    R.flow.continuous.comp (continuous_fst.prodMk (hp.continuous.comp continuous_snd))⟩
  let A := hp.liftHomotopy H (ContinuousMap.id E) (fun e => R.initial (p e))
  have he (t e) : p (A (t,e)) = R.flow (t,p e) :=
    congrFun (hp.liftHomotopy_lifts H (ContinuousMap.id E) (fun e => R.initial (p e))) (t,e)
  have h0 (e) : A (0,e) = e := hp.liftHomotopy_zero H _ _ e
  refine ⟨A,h0,he,?_⟩
  intro t e hk
  have same : (fun s : unitInterval => A (s,e)) = fun _ => e := by
    apply hp.eq_of_comp_eq (A.continuous.comp (continuous_id.prodMk continuous_const)) continuous_const _ 0 (h0 e)
    exact funext fun s => (he s e).trans (R.fixed s _ hk)
  exact congrFun same t

include R

/-- Maps of covers over a common base are determined on a deformation
retract even when the total spaces are disconnected. -/
theorem CoverCoreRetraction.cover_maps_ext (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f g : C(E,F)) (hf : ∀ e, q (f e) = p e) (hg : ∀ e, q (g e) = p e)
    (he : ∀ e, p e ∈ K → f e = g e) : f = g := by
  obtain ⟨A,h0,hA,_⟩ := R.lift hp
  ext e
  have hcore : p (A (1,e)) ∈ K := hA 1 e ▸ R.terminal _
  have same : (fun s => f (A (s,e))) = fun s => g (A (s,e)) := by
    have hpath : Continuous (fun s : unitInterval => A (s,e)) :=
      A.continuous.comp (continuous_id.prodMk continuous_const)
    apply hq.eq_of_comp_eq (f.continuous.comp hpath) (g.continuous.comp hpath) _ 1 (he _ hcore)
    exact funext fun s => (hf _).trans (hg _).symm
  simpa only [h0] using congrFun same 0

/-- Every covering map over the core extends to a continuous covering
morphism over the entire strongly retracted base. -/
theorem CoverCoreRetraction.extend_cover_map (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : C({e : E // p e ∈ K}, {y : F // q y ∈ K})) (hf : ∀ e, q (f e).1 = p e.1) :
    ∃ G : C(E,F), (∀ e, q (G e) = p e) ∧ ∀ e : {e : E // p e ∈ K}, G e.1 = (f e).1 := by
  obtain ⟨A,_,hA,hfix⟩ := R.lift hp
  let a : C(E,{e : E // p e ∈ K}) := ⟨fun e => ⟨A (1,e),hA 1 e ▸ R.terminal _⟩,
    (A.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let g : C(E,F) := ⟨fun e => (f (a e)).1,continuous_subtype_val.comp (f.continuous.comp a.continuous)⟩
  let H : C(unitInterval × E,B) := ⟨fun u => R.flow (unitInterval.symm u.1,p u.2),R.flow.continuous.comp
    ((unitInterval.continuous_symm.comp continuous_fst).prodMk (hp.continuous.comp continuous_snd))⟩
  have h0 (e) : H (0,e) = q (g e) := by
    change R.flow (unitInterval.symm 0,p e) = q (f (a e)).1
    rw [unitInterval.symm_zero,hf]
    exact (hA 1 e).symm
  let Q := hq.liftHomotopy H g h0
  have hQ (s e) : q (Q (s,e)) = R.flow (unitInterval.symm s,p e) :=
    congrFun (hq.liftHomotopy_lifts H g h0) (s,e)
  let G : C(E,F) := ⟨fun e => Q (1,e),Q.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨G,fun e => (hQ 1 e).trans (by rw [unitInterval.symm_one,R.initial]),?_⟩
  intro e
  have ha : a e.1 = e := Subtype.ext (hfix 1 e.1 e.2)
  have hs : Q (0,e.1) = (f e).1 := (hq.liftHomotopy_zero H g h0 e.1).trans (congrArg (fun v => (f v).1) ha)
  have heq : (fun s : unitInterval => Q (s,e.1)) = fun _ => (f e).1 := by
    apply hq.eq_of_comp_eq (Q.continuous.comp (continuous_id.prodMk continuous_const)) continuous_const _ 0 hs
    exact funext fun s => (hQ _ _).trans ((R.fixed _ _ e.2).trans (hf e).symm)
  exact congrFun heq 1

/-- A given identification of two covers on a deformation retract extends
uniquely to a homeomorphism of covers on the full base. -/
theorem CoverCoreRetraction.cover_isomorphism_extends (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : {e : E // p e ∈ K} ≃ₜ {y : F // q y ∈ K}) (hf : ∀ e, q (f e).1 = p e.1) :
    ∃! G : E ≃ₜ F, (∀ e, q (G e) = p e) ∧ ∀ e : {e : E // p e ∈ K}, G e.1 = (f e).1 := by
  obtain ⟨u,hu,huK⟩ := R.extend_cover_map hp hq ⟨f,f.continuous⟩ hf
  have hfi (y) : p (f.symm y).1 = q y.1 := (hf (f.symm y)).symm.trans (congrArg (fun z => q z.1) (f.apply_symm_apply y))
  obtain ⟨v,hv,hvK⟩ := R.extend_cover_map hq hp ⟨f.symm,f.symm.continuous⟩ hfi
  have hleft : v.comp u = ContinuousMap.id E := by
    apply R.cover_maps_ext hp hp _ _ (fun e => (hv _).trans (hu e)) (fun _ => rfl)
    intro x hx
    let e := (⟨x,hx⟩ : {e : E // p e ∈ K})
    change v (u e.1) = e.1
    rw [huK e]
    exact (hvK (f e)).trans (congrArg Subtype.val (f.symm_apply_apply e))
  have hright : u.comp v = ContinuousMap.id F := by
    apply R.cover_maps_ext hq hq _ _ (fun e => (hu _).trans (hv e)) (fun _ => rfl)
    intro y hy
    let e := (⟨y,hy⟩ : {e : F // q e ∈ K})
    change u (v e.1) = e.1
    rw [hvK e]
    exact (huK (f.symm e)).trans (congrArg Subtype.val (f.apply_symm_apply e))
  let G : E ≃ₜ F := ⟨⟨u,v,fun e => DFunLike.congr_fun hleft e,fun y => DFunLike.congr_fun hright y⟩,u.continuous,v.continuous⟩
  refine ⟨G,⟨hu,huK⟩,?_⟩
  intro T hT
  have hEq := R.cover_maps_ext hp hq ⟨T,T.continuous⟩ u hT.1 hu
    (fun x hx => (hT.2 ⟨x,hx⟩).trans (huK ⟨x,hx⟩).symm)
  exact Homeomorph.ext fun x => DFunLike.congr_fun hEq x

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.CoverCoreRetraction.cover_isomorphism_extends
