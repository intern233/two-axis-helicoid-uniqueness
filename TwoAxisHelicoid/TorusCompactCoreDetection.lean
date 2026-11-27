import TwoAxisHelicoid.TorusLoopBasisDisplacements
import Mathlib.RingTheory.Noetherian.Orzech

namespace TwoAxisHelicoid
open Complex Set

/-- Surjectivity already implies injectivity for a homomorphism between
fundamental groups of two closed complex tori. The full lattice has rank
two over the integers. -/
theorem torus_fundamental_group_injective_of_surjective (L A : PeriodPair) (z w : ℂ)
    (f : FundamentalGroup (PeriodTorus L) (periodTorusProjection L z) →*
      FundamentalGroup (PeriodTorus A) (periodTorusProjection A w)) (hf : Function.Surjective f) : Function.Injective f := by
  let e := periodTorusFundamentalGroupEquiv L z
  let u := periodTorusFundamentalGroupEquiv A w
  let g := u.toMonoidHom.comp (f.comp e.symm.toMonoidHom)
  let a : (ℤ × ℤ) →+ (ℤ × ℤ) := {
    toFun := fun x => Multiplicative.toAdd (g (Multiplicative.ofAdd x))
    map_zero' := g.map_one
    map_add' := fun x y => g.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) }
  have hg : Function.Surjective g := u.surjective.comp (hf.comp e.symm.surjective)
  have ha : Function.Injective a := IsNoetherian.injective_of_surjective_endomorphism a.toIntLinearMap hg
  intro x y h
  apply e.injective
  apply Multiplicative.toAdd.injective
  apply ha
  change Multiplicative.toAdd (u (f (e.symm (e x)))) = Multiplicative.toAdd (u (f (e.symm (e y))))
  rw [e.symm_apply_apply,e.symm_apply_apply,h]

/-- A map collapsing the complement of a marked core and recovering its
two reference loops forces the two transported loops to generate the
ambient torus. A second region killed by this map can carry no nontrivial
ambient loop class. -/
theorem detecting_map_forces_generators_and_trivial_complement (L A : PeriodPair) (z : ℂ)
    (g : Fin 2 → FundamentalGroup (PeriodTorus L) (periodTorusProjection L z))
    (f : FundamentalGroup (PeriodTorus L) (periodTorusProjection L z) →*
      FundamentalGroup (PeriodTorus A) (puncturedTorusCenter A).1)
    (h : ∀ i, f (g i) = periodTorusGeneratorClass A i) :
    (∀ v, ∃ m n : ℤ, v = g 0 ^ m * g 1 ^ n) ∧ ∀ v, f v = 1 → v = 1 := by
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨m,n,hv⟩ := periodTorusFundamentalGroup_generated A v
    exact ⟨g 0^m*g 1^n,by rw [map_mul,map_zpow,map_zpow,h,h,hv]⟩
  have hinj := torus_fundamental_group_injective_of_surjective L A z (periodBasisLine A 0 0) f hsurj
  refine ⟨?_,fun v hv => hinj (hv.trans f.map_one.symm)⟩
  intro v
  obtain ⟨m,n,he⟩ := periodTorusFundamentalGroup_generated A (f v)
  have hm : f (g 0^m*g 1^n) = f v := by rw [map_mul,map_zpow,map_zpow,h,h,he]
  exact ⟨m,n,hinj hm.symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.detecting_map_forces_generators_and_trivial_complement
