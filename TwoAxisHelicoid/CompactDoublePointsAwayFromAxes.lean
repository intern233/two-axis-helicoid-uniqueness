import TwoAxisHelicoid.CertifiedCompactDoublePoints
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace TwoAxisHelicoid
open Set Metric Topology

/-- If the compact set of double points avoids the square of a closed
set A, all pairs have at least one endpoint in a compact set disjoint
from A. The complement is an injectivity neighborhood of A and of the
whole end. -/
theorem compact_collision_projection_off_injective_set {M E : Type*} [MetricSpace M]
    (F : M → E) {A K : Set M} (ac : IsClosed A) (ne : A.Nonempty) (axis : InjOn F A)
    (kc : IsCompact K) (dc : IsCompact (immersionDoublePoints F)) (sat : immersionDoublePoints F ⊆ K ×ˢ K) :
    ∃ B : Set M, IsCompact B ∧ B⊆K ∧ Disjoint A B ∧ InjOn F Bᶜ ∧
      (Function.Injective F ↔ ∀ x∈B, ∀ y∈K, F x=F y → x=y) := by
  let D := immersionDoublePoints F
  have finish (B : Set M) (bc : IsCompact B) (sub : B⊆K) (away : Disjoint A B)
      (hit : ∀ p∈D, p.1∈B ∨ p.2∈B) : ∃ B : Set M, IsCompact B ∧ B⊆K ∧ Disjoint A B ∧ InjOn F Bᶜ ∧
        (Function.Injective F ↔ ∀ x∈B, ∀ y∈K, F x=F y → x=y) := by
    refine ⟨B,bc,sub,away,?_,⟨fun h _ _ _ _ e => h e,?_⟩⟩
    · intro x hx y hy e
      by_contra nd
      exact (hit (x,y) ⟨e,nd⟩).elim hx hy
    · intro h x y e
      by_contra nd
      have mem : (x,y)∈D := ⟨e,nd⟩
      exact (hit (x,y) mem).elim (fun hx => nd (h x hx y (sat mem).2 e))
        (fun hy => nd (h y hy x (sat mem).1 e.symm).symm)
  by_cases dn : D.Nonempty
  · let d := fun p : M × M => max (infDist p.1 A) (infDist p.2 A)
    have cont : Continuous d := ((continuous_infDist_pt A).comp continuous_fst).max ((continuous_infDist_pt A).comp continuous_snd)
    obtain ⟨p,hp,bound⟩ := dc.exists_isMinOn dn cont.continuousOn
    have pos : 0<d p := by
      by_contra! h
      obtain ⟨e,n⟩ := hp
      have a := (ac.mem_iff_infDist_zero ne).mpr (le_antisymm ((le_max_left _ _).trans h) infDist_nonneg)
      have b := (ac.mem_iff_infDist_zero ne).mpr (le_antisymm ((le_max_right _ _).trans h) infDist_nonneg)
      exact n (axis a b e)
    let B := K ∩ {q : M | d p≤ infDist q A}
    refine finish B (kc.inter_right (isClosed_le continuous_const (continuous_infDist_pt A))) inter_subset_left
      (disjoint_left.mpr fun x hx hB => ?_) ?_
    · exact pos.not_ge ((show d p≤ infDist x A from hB.2).trans_eq (infDist_zero_of_mem hx))
    · intro q hq
      rcases le_max_iff.mp (show d p≤max (infDist q.1 A) (infDist q.2 A) from bound hq) with a|b
      · exact Or.inl ⟨(sat hq).1,a⟩
      · exact Or.inr ⟨(sat hq).2,b⟩
  · exact finish ∅ isCompact_empty (empty_subset _) (disjoint_empty _) (fun q hq => (dn ⟨q,hq⟩).elim)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_collision_projection_off_injective_set
