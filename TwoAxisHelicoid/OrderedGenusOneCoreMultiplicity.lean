import TwoAxisHelicoid.DisjointTorusCoreObstruction
import TwoAxisHelicoid.OrderedCoreSections
import Mathlib.Topology.Homotopy.Lifting

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Two distinct points over one point yield two distinct points over all
points of a path-connected base, using actual covering path transport. -/
theorem covering_two_points_in_every_fiber {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PathConnectedSpace X] {p : E → X} (hp : IsCoveringMap p) (a b : E) (hab : a ≠ b)
    (he : p a = p b) (x : X) : ∃ u v, p u = x ∧ p v = x ∧ u ≠ v := by
  let γ : Path.Homotopic.Quotient (p a) x := .mk (PathConnectedSpace.somePath _ _)
  have hleft (u : p ⁻¹' {p a}) : hp.monodromy γ.symm (hp.monodromy γ u) = u := by
    rw [← hp.monodromy_trans_apply,γ.trans_symm,hp.monodromy_refl]
    rfl
  let u := hp.monodromy γ ⟨a,rfl⟩
  let v := hp.monodromy γ ⟨b,he.symm⟩
  refine ⟨u.1,v.1,u.2,v.2,?_⟩
  intro h
  have h' : u = v := Subtype.ext h
  have eq := congrArg (hp.monodromy γ.symm) h'
  change hp.monodromy γ.symm (hp.monodromy γ ⟨a,rfl⟩) = hp.monodromy γ.symm (hp.monodromy γ ⟨b,he.symm⟩) at eq
  rw [hleft,hleft] at eq
  exact hab (congrArg Subtype.val eq)

/-- A proper finite normal-graph cover above a genus-one core is a
single sheet when the total space embeds as an open subset of another
torus. The actual domain need not be connected and the degree is not an
input. -/
theorem ordered_normal_cover_of_genus_one_core_is_homeomorphism
    {A L : PeriodPair} (C : TorusGeneratingCoreModel A) {E : Type*} [TopologicalSpace E] [T2Space E]
    (j : E → PeriodTorus L) (hj : IsOpenEmbedding j) {p : E → C.carrier} {h : E → ℝ}
    (hp : IsProperMap p) (hl : IsLocalHomeomorph p) (hs : Function.Surjective p) (hh : Continuous h)
    (hsep : ∀ a b, p a = p b → h a = h b → a = b) : IsHomeomorph p := by
  let := C.pathConnected
  refine ⟨hp.continuous,hl.isOpenMap,?_,hs⟩
  intro a b he
  by_contra hab
  have hm := covering_two_points_in_every_fiber (proper_local_homeomorph_isCoveringMap hp hl) a b hab he
  obtain ⟨f,g,hf,hg,hd⟩ := ordered_cover_has_two_disjoint_open_sections hp hl hh hsep hm
  apply disjoint_genus_one_cores_impossible C C (j ∘ f) (j ∘ g) (hj.comp hf) (hj.comp hg)
  apply Set.disjoint_left.mpr
  rintro _ ⟨x,rfl⟩ ⟨y,hxy⟩
  exact Set.disjoint_left.mp hd ⟨x,rfl⟩ ⟨y,hj.injective hxy⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ordered_normal_cover_of_genus_one_core_is_homeomorphism
