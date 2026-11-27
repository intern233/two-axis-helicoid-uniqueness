import TwoAxisHelicoid.TorusSignCharacter

namespace TwoAxisHelicoid
open Set

def coverFiberMap {E F B : Type*} {p : E → B} {q : F → B}
    (f : E → F) (hf : ∀ x, q (f x) = p x) (b : B) : p ⁻¹' {b} → q ⁻¹' {b} :=
  fun x => ⟨f x.1,(hf x.1).trans x.2⟩

/-- A continuous map over a common base commutes with actual covering
monodromy. No equality of monodromy is taken as an extra assumption. -/
theorem coverFiberMap_monodromy {E F B : Type*}
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    {p : E → B} {q : F → B} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : E → F) (hc : Continuous f) (hf : ∀ x, q (f x) = p x)
    {b c : B} (γ : Path.Homotopic.Quotient b c) (x : p ⁻¹' {b}) :
    coverFiberMap f hf c (hp.monodromy γ x) =
      hq.monodromy γ (coverFiberMap f hf b x) := by
  obtain ⟨γ⟩ := γ
  let α := hp.liftPath γ x.1 (γ.source.trans x.2.symm)
  let β : C(unitInterval,F) := ⟨f ∘ α,hc.comp α.continuous⟩
  have hβ : q ∘ β = γ := by
    funext s
    exact (hf (α s)).trans (congrFun (hp.liftPath_lifts γ x.1 (γ.source.trans x.2.symm)) s)
  have hβ0 : β 0 = (coverFiberMap f hf b x).1 := by
    change f (α 0) = f x.1
    rw [hp.liftPath_zero]
  apply Subtype.ext
  change f (hp.monodromy (.mk γ) x).1 = _
  rw [hp.coe_monodromy_mk]
  exact (hq.monodromy_eq_apply_one hβ hβ0).symm

theorem coverFiberMap_bijective_of_path {E F B : Type*}
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    {p : E → B} {q : F → B} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : E → F) (hc : Continuous f) (hf : ∀ x, q (f x) = p x)
    {b c : B} (γ : Path b c) (hb : Function.Bijective (coverFiberMap f hf b)) :
    Function.Bijective (coverFiberMap f hf c) := by
  have hpγ := hp.monodromy_bijective (.mk γ)
  have hqγ := hq.monodromy_bijective (.mk γ)
  constructor
  · intro x y hxy
    obtain ⟨x₀,rfl⟩ := hpγ.surjective x
    obtain ⟨y₀,rfl⟩ := hpγ.surjective y
    rw [coverFiberMap_monodromy hp hq f hc hf,coverFiberMap_monodromy hp hq f hc hf] at hxy
    exact congrArg (hp.monodromy (.mk γ)) (hb.injective (hqγ.injective hxy))
  · intro y
    obtain ⟨y₀,rfl⟩ := hqγ.surjective y
    obtain ⟨x₀,hx₀⟩ := hb.surjective y₀
    refine ⟨hp.monodromy (.mk γ) x₀,?_⟩
    rw [coverFiberMap_monodromy hp hq f hc hf,hx₀]

/-- For a path connected base, a map of covers which is a bijection on
one actual fiber is a bijection of the complete total spaces. -/
theorem coverMap_bijective_of_one_fiber {E F B : Type*}
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [PathConnectedSpace B]
    {p : E → B} {q : F → B} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : E → F) (hc : Continuous f) (hf : ∀ x, q (f x) = p x)
    (b : B) (hb : Function.Bijective (coverFiberMap f hf b)) : Function.Bijective f := by
  have hbij (c : B) : Function.Bijective (coverFiberMap f hf c) :=
    coverFiberMap_bijective_of_path hp hq f hc hf (PathConnectedSpace.somePath b c) hb
  constructor
  · intro x y hxy
    have hy : p y = p x := (hf y).symm.trans ((congrArg q hxy.symm).trans (hf x))
    exact congrArg Subtype.val ((hbij (p x)).injective
      (show coverFiberMap f hf (p x) ⟨x,rfl⟩ = coverFiberMap f hf (p x) ⟨y,hy⟩ from
        Subtype.ext hxy))
  · intro y
    obtain ⟨x,hx⟩ := (hbij (q y)).surjective ⟨y,rfl⟩
    exact ⟨x.1,congrArg Subtype.val hx⟩

theorem coverMap_isLocalHomeomorph {E F B : Type*}
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    {p : E → B} {q : F → B} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (f : E → F) (hc : Continuous f) (hf : ∀ x, q (f x) = p x) : IsLocalHomeomorph f := by
  have he : q ∘ f = p := funext hf
  have hh := hp.isLocalHomeomorph
  rw [← he] at hh
  exact hh.of_comp hq.isLocalHomeomorph hc

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.coverMap_bijective_of_one_fiber
