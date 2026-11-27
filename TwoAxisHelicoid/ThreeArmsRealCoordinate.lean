import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Fintype.Pigeonhole

namespace TwoAxisHelicoid
open Set

/-- Three or more arcs from one point, disjoint at positive times, cannot
be mapped continuously and injectively to a real line. The proof uses
the intermediate value theorem on the two arcs which start on the same side. -/
theorem no_real_coordinate_on_three_arms {ι : Type*} [Fintype ι]
    (many : 2<Fintype.card ι) {r c : ℝ} (positive : 0<r) (u : ι → ℝ → ℝ)
    (cont : ∀ i, ContinuousOn (u i) (Icc 0 r)) (center : ∀ i, u i 0=c)
    (away : ∀ i, u i r≠c)
    (separated : ∀ i j s t, s∈Ioc 0 r → t∈Ioc 0 r → u i s=u j t → i=j) : False := by
  classical
  let side := fun i => decide (c<u i r)
  obtain ⟨i,j,different,same⟩ := Fintype.exists_ne_map_eq_of_card_lt side (by simpa using many)
  have order : (c<u i r) ↔ c<u j r := decide_eq_decide.mp same
  have miss (i j : ι) (ne : i≠j) : u i r∉uIcc c (u j r) := by
    intro inside
    have hits := intermediate_value_uIcc (a:=(0:ℝ)) (b:=r) (f:=u j)
      (by simpa only [uIcc_of_le positive.le] using cont j)
    rw [center] at hits
    obtain ⟨s,hs,eq⟩ := hits inside
    rw [uIcc_of_le positive.le] at hs
    have nz : s≠0 := by rintro rfl; exact away i (eq.symm.trans (center j))
    exact ne (separated i j r s ⟨positive,le_rfl⟩ ⟨lt_of_le_of_ne hs.1 nz.symm,hs.2⟩ eq.symm)
  by_cases a : c<u i r
  · have b := order.mp a
    rcases le_total (u i r) (u j r) with h|h
    · exact miss i j different (mem_uIcc_of_le a.le h)
    · exact miss j i different.symm (mem_uIcc_of_le b.le h)
  · have b : u j r≤c := le_of_not_gt (fun h => a (order.mpr h))
    rcases le_total (u i r) (u j r) with h|h
    · exact miss j i different.symm (mem_uIcc_of_ge h b)
    · exact miss i j different (mem_uIcc_of_ge h (le_of_not_gt a))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.no_real_coordinate_on_three_arms
