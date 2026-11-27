import TwoAxisHelicoid.RectanglePhaseGap
import Mathlib.Topology.Order.Compact

namespace TwoAxisHelicoid
open Set Topology

/-- The extrema of a continuous phase on the compact rectangle lie
on its two horizontal edges if it has no local extremum elsewhere,
including on either vertical edge. All remaining phase values lie
strictly between the two constant boundary values. -/
theorem rectangle_phase_strict_between_edges {F : unitInterval × unitInterval → ℝ} (cf : Continuous F)
    (no : ∀ q : unitInterval × unitInterval, q.2≠0 → q.2≠1 → ¬IsLocalExtr F q)
    {a b : ℝ} (bottom : ∀ x, F (x,0)=a) (top : ∀ x, F (x,1)=b) :
    ∀ q : unitInterval × unitInterval, q.2≠0 → q.2≠1 → F q ∈ Ioo (min a b) (max a b) := by
  obtain ⟨p,_,hm⟩ := isCompact_univ.exists_isMinOn univ_nonempty cf.continuousOn
  obtain ⟨v,_,hM⟩ := isCompact_univ.exists_isMaxOn univ_nonempty cf.continuousOn
  have ends {s : unitInterval × unitInterval} (hs : IsLocalExtr F s) : F s=a ∨ F s=b := by
    by_cases low : s.2=0
    · exact Or.inl (by rw [← Prod.eta s,low,bottom])
    by_cases high : s.2=1
    · exact Or.inr (by rw [← Prod.eta s,high,top])
    exact (no s low high hs).elim
  have pbound : min a b≤F p := by
    rcases ends (Or.inl (hm.isLocalMin (Filter.univ_mem))) with e | e <;> simp [e]
  have vbound : F v≤max a b := by
    rcases ends (Or.inr (hM.isLocalMax (Filter.univ_mem))) with e | e <;> simp [e]
  have lower (q) : min a b≤F q := pbound.trans (hm (mem_univ q))
  have upper (q) : F q≤max a b := (hM (mem_univ q)).trans vbound
  intro q y0 y1
  constructor
  · apply (lower q).lt_of_ne
    intro e
    apply no q y0 y1
    left
    exact Filter.Eventually.of_forall fun x => e ▸ lower x
  · apply (upper q).lt_of_ne
    intro e
    apply no q y0 y1
    right
    exact Filter.Eventually.of_forall fun x => e.symm ▸ upper x

/-- A horizontal-axis test and the disk maximum principle suffice to
exclude every integral phase leaf in the disk. This formulation uses
two-dimensional intermediate values and requires no regularity or
finiteness hypotheses on individual level curves. -/
theorem rectangle_phase_excludes_comparison_leaves (H F : unitInterval × unitInterval → ℝ)
    (cH : Continuous H) (cF : Continuous F)
    (vertical : (∀ y, H (0,y)≤0 ∧ 0≤H (1,y)) ∨ (∀ y, 0≤H (0,y) ∧ H (1,y)≤0))
    (vl : ∀ y : unitInterval, y ≠ 0 → y ≠ 1 → H (0,y) ≠ 0 ∧ H (1,y) ≠ 0)
    (n m : ℤ) (bottom : ∀ x, F (x,0)=n*Real.pi) (top : ∀ x, F (x,1)=m*Real.pi)
    (axis : ∀ q : unitInterval × unitInterval, q.1≠0 → q.1≠1 → q.2≠0 → q.2≠1 →
      H q=0 → ∀ k : ℤ, F q≠k*Real.pi)
    (ext : ∀ q : unitInterval × unitInterval, q.2≠0 → q.2≠1 → ¬IsLocalExtr F q) :
    ∀ q : unitInterval × unitInterval, q.2≠0 → q.2≠1 → ∀ k : ℤ, F q ≠ k*Real.pi := by
  have gap := rectangle_phase_gap_of_no_horizontal_axis H F cH cF vertical vl n m bottom top axis
  intro q y0 y1 k e
  have he := rectangle_phase_strict_between_edges cF ext bottom top q y0 y1
  rw [e] at he
  have ord : (n<k ∧ k<m) ∨ (m<k ∧ k<n) := by
    by_cases nm : n≤m
    · have le := mul_le_mul_of_nonneg_right (show (n:ℝ)≤m by exact_mod_cast nm) Real.pi_pos.le
      rw [min_eq_left le,max_eq_right le] at he
      exact Or.inl ⟨by exact_mod_cast (lt_of_mul_lt_mul_right he.1 Real.pi_pos.le),
        by exact_mod_cast (lt_of_mul_lt_mul_right he.2 Real.pi_pos.le)⟩
    · have le := mul_le_mul_of_nonneg_right (show (m:ℝ)≤n by exact_mod_cast (le_of_not_ge nm)) Real.pi_pos.le
      rw [min_eq_right le,max_eq_left le] at he
      exact Or.inr ⟨by exact_mod_cast (lt_of_mul_lt_mul_right he.1 Real.pi_pos.le),
        by exact_mod_cast (lt_of_mul_lt_mul_right he.2 Real.pi_pos.le)⟩
  rw [abs_le] at gap
  rcases ord with h | h <;> omega

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rectangle_phase_strict_between_edges
#print axioms TwoAxisHelicoid.rectangle_phase_excludes_comparison_leaves
