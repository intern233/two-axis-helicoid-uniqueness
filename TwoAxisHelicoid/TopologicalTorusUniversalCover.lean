import TwoAxisHelicoid.TorusActualLifts
import TwoAxisHelicoid.PeriodTorusConjugation

namespace TwoAxisHelicoid
open Complex Set Function Filter Topology
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]

/-- The lifts between any simply connected covering of a topological torus
and its standard covering plane are mutually inverse homeomorphisms. -/
theorem topological_torus_cover_equivalence (L : PeriodPair) {p : E → PeriodTorus L}
    (hp : IsCoveringMap p) (a : E) :
    ∃ F : E ≃ₜ ℂ, ∀ x, periodTorusProjection L (F x) = p x := by
  let π := periodTorusProjection L
  obtain ⟨b,hb⟩ := (Quotient.mk_surjective : Surjective π) (p a)
  let P : C(E,PeriodTorus L) := ⟨p,hp.continuous⟩
  let Q : C(ℂ,PeriodTorus L) := ⟨π,QuotientAddGroup.continuous_mk⟩
  have hπ := periodTorusProjection_isCoveringMap L
  obtain ⟨F,⟨hF,hπF⟩,_⟩ := hπ.existsUnique_continuousMap_lifts P a b hb
  obtain ⟨G,⟨hG,hpG⟩,_⟩ := hp.existsUnique_continuousMap_lifts Q b a hb.symm
  have hleft : G ∘ F = id := hp.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id
    (funext fun x => (congrFun hpG (F x)).trans (congrFun hπF x)) a ((congrArg G hF).trans hG)
  have hright : F ∘ G = id := hπ.eq_of_comp_eq (F.continuous.comp G.continuous) continuous_id
    (funext fun x => (congrFun hπF (G x)).trans (congrFun hpG x)) b ((congrArg F hG).trans hF)
  exact ⟨⟨⟨F,G,congrFun hleft,congrFun hright⟩,F.continuous,G.continuous⟩,congrFun hπF⟩

/-- Two continuous self-lifts of such a torus covering commute. In standard
covering-plane coordinates each is a translation by a lattice period. -/
theorem topological_torus_cover_lifts_commute (L : PeriodPair) {p : E → PeriodTorus L}
    (hp : IsCoveringMap p) (a : E) {f g : E → E} (hf : Continuous f) (hg : Continuous g)
    (hpF : ∀ z, p (f z) = p z) (hpG : ∀ z, p (g z) = p z) : f ∘ g = g ∘ f := by
  obtain ⟨τ,ht⟩ := topological_torus_cover_equivalence L hp a
  have hlift {h : E → E} (hh : Continuous h) (hl : ∀ x, p (h x) = p x) :
      ∃ d : ℂ, ∀ x, τ (h x) = τ x+d := by
    let d := τ (h a)-τ a
    have hd : d ∈ L.lattice := (periodTorusProjection_eq_iff L _ _).mp
      ((ht a).trans ((hl a).symm.trans (ht (h a)).symm))
    have he : τ ∘ h = fun x => τ x+d := by
      apply (periodTorusProjection_isCoveringMap L).eq_of_comp_eq (τ.continuous.comp hh)
        (τ.continuous.add continuous_const) _ a
      · change τ (h a) = τ a+(τ (h a)-τ a)
        ring
      · exact funext fun x => (ht (h x)).trans ((hl x).trans
          ((ht x).symm.trans (periodTorusProjection_add_lattice L (τ x) d hd).symm))
    exact ⟨d,congrFun he⟩
  obtain ⟨b,hb⟩ := hlift hf hpF
  obtain ⟨c,hc⟩ := hlift hg hpG
  change f ∘ g = g ∘ f
  ext x
  apply τ.injective
  change τ (f (g x)) = τ (g (f x))
  rw [hb,hc,hc,hb]
  ring

/-- For a general simply connected cover, deck homeomorphisms act
transitively on each fiber. -/
theorem simply_connected_cover_deck_transitive {M : Type*} [TopologicalSpace M]
    {p : E → M} (hp : IsCoveringMap p) {x y : E} (hxy : p x = p y) :
    ∃ f : E ≃ₜ E, f x = y ∧ ∀ z, p (f z) = p z := by
  let P : C(E,M) := ⟨p,hp.continuous⟩
  obtain ⟨F,⟨hF,hpF⟩,_⟩ := hp.existsUnique_continuousMap_lifts P x y hxy.symm
  obtain ⟨G,⟨hG,hpG⟩,_⟩ := hp.existsUnique_continuousMap_lifts P y x hxy
  have hl : G ∘ F = id := hp.eq_of_comp_eq (G.continuous.comp F.continuous) continuous_id
    (funext fun z => (congrFun hpG (F z)).trans (congrFun hpF z)) x ((congrArg G hF).trans hG)
  have hr : F ∘ G = id := hp.eq_of_comp_eq (F.continuous.comp G.continuous) continuous_id
    (funext fun z => (congrFun hpF (G z)).trans (congrFun hpG z)) y ((congrArg F hG).trans hF)
  exact ⟨⟨⟨F,G,congrFun hl,congrFun hr⟩,F.continuous,G.continuous⟩,hF,congrFun hpF⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.topological_torus_cover_equivalence
#print axioms TwoAxisHelicoid.topological_torus_cover_lifts_commute
