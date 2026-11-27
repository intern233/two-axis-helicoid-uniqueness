import TwoAxisHelicoid.CertifiedCompactDoublePoints
import Mathlib.Topology.Compactness.Compact

namespace TwoAxisHelicoid
open Set Filter Topology

/-- For a continuous family of immersions, injectivity is open when
double points are uniformly confined to a compact set of parameter
pairs and a single local chart remains injective near each diagonal
point. The compact set may contain the diagonal. -/
theorem injectivity_open_from_uniform_compact_pairs {T M E : Type*}
    [TopologicalSpace T] [TopologicalSpace M] [TopologicalSpace E] [T2Space E]
    (F : T → M → E) {t : T} (inj : Function.Injective (F t))
    (cont : ∀ q : M, ContinuousAt (fun a : T × M => F a.1 a.2) (t,q))
    (charts : ∀ q : M, ∃ V ∈ 𝓝 t, ∃ U ∈ 𝓝 q, ∀ s ∈ V, InjOn (F s) U)
    {K : Set (M × M)} (hK : IsCompact K)
    (tight : ∀ᶠ s in 𝓝 t, immersionDoublePoints (F s) ⊆ K) :
    ∀ᶠ s in 𝓝 t, Function.Injective (F s) := by
  let S := {a : T × (M × M) | a.2.1 = a.2.2 ∨ F a.1 a.2.1 ≠ F a.1 a.2.2}
  have tube : ({t} : Set T) ×ˢ K ⊆ interior S := by
    rintro ⟨s,x,y⟩ ⟨hs,_⟩
    have eqt : s=t := hs
    subst s
    apply mem_interior_iff_mem_nhds.mpr
    by_cases eq : x=y
    · subst y
      obtain ⟨V,hV,U,hU,hi⟩ := charts x
      have n : V ×ˢ (U ×ˢ U) ∈ 𝓝 (t,x,x) := prod_mem_nhds hV (prod_mem_nhds hU hU)
      apply mem_of_superset n
      intro a ha
      change a.2.1=a.2.2 ∨ F a.1 a.2.1 ≠ F a.1 a.2.2
      exact or_iff_not_imp_left.mpr (fun neq same => neq (hi a.1 ha.1 ha.2.1 ha.2.2 same))
    · have cx : ContinuousAt (fun a : T × (M × M) => F a.1 a.2.1) (t,x,y) :=
        (cont x).comp (x := (t,x,y)) (f := fun a : T × (M × M) => (a.1,a.2.1)) (by fun_prop)
      have cy : ContinuousAt (fun a : T × (M × M) => F a.1 a.2.2) (t,x,y) :=
        (cont y).comp (x := (t,x,y)) (f := fun a : T × (M × M) => (a.1,a.2.2)) (by fun_prop)
      exact ((cx.ne_iff_eventually_ne cy).mp (fun h => eq (inj h))).mono (fun _ ne => Or.inr ne)
  obtain ⟨V,U,ho,_,hV,hU,hvu⟩ := generalized_tube_lemma isCompact_singleton hK isOpen_interior tube
  filter_upwards [ho.mem_nhds (hV (mem_singleton t)),tight] with s hs hbound
  intro x y same
  by_contra neq
  have hpair : (x,y) ∈ immersionDoublePoints (F s) := ⟨same,neq⟩
  have inside : (s,x,y) ∈ interior S := hvu ⟨hs,hU (hbound hpair)⟩
  exact (interior_subset inside : (s,x,y) ∈ S).elim neq (fun h => h same)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.injectivity_open_from_uniform_compact_pairs
