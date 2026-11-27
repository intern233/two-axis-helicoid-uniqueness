import TwoAxisHelicoid.TangentPhaseMonodromy
import Mathlib.GroupTheory.Commutator.Basic

namespace TwoAxisHelicoid
open Set
open scoped commutatorElement

/-- The two sheets make the monodromies of any double covering commute
at a shared base point. -/
theorem two_sheet_permutations_commute {A : Type*} (a b : A) (hab : a ≠ b)
    (h : ∀ x : A, x = a ∨ x = b) (p q : Equiv.Perm A) : p*q = q*p := by
  have classify (g : Equiv.Perm A) : (g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a) := by
    have ne := g.injective.ne hab
    rcases h (g a) with ha | ha <;> rcases h (g b) with hb | hb <;> simp_all
  ext x
  change p (q x) = q (p x)
  rcases classify p with p' | p' <;> rcases classify q with q' | q' <;>
    rcases h x with rfl | rfl <;> simp only [p'.1,p'.2,q'.1,q'.2]

/-- A commutator of punctured-surface loops always has trivial ambient
spin monodromy. The conclusion uses the actual quaternion double cover. -/
theorem quaternion_monodromy_commutator (p : OrthonormalTangentPair)
    (x y : FundamentalGroup OrthonormalTangentPair p) :
    unitQuaternionFrame_isCoveringMap.monodromyPerm p ⁅x,y⁆ = 1 := by
  obtain ⟨s,hs⟩ := unitQuaternionFrame_surjective p
  let a : unitQuaternionFrame ⁻¹' {p} := ⟨s,hs⟩
  let b : unitQuaternionFrame ⁻¹' {p} := ⟨unitQuaternionAntipode s,(unitQuaternionFrame_antipode s).trans hs⟩
  have hab : a ≠ b := fun h => unitQuaternionAntipode_ne s (congrArg Subtype.val h).symm
  have htwo (u : unitQuaternionFrame ⁻¹' {p}) : u = a ∨ u = b := by
    have hf : unitQuaternionFrame u.1 = unitQuaternionFrame s := u.2.trans hs.symm
    rcases (quaternion_frame_fibers_deck _ _).mp hf with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact two_sheet_permutations_commute a b hab htwo _ _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.quaternion_monodromy_commutator
