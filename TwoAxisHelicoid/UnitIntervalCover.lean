import Mathlib.Tactic

namespace TwoAxisHelicoid

theorem exists_unit_subinterval {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx0 : 0 ≤ x) (hxN : x ≤ (N : ℝ)) :
    ∃ i : Fin N, (i : ℝ) ≤ x ∧ x ≤ (i : ℝ)+1 := by
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases hx : x ≤ (n : ℝ)
    · by_cases hn : 0 < n
      · obtain ⟨i,hil,hiu⟩ := ih hn hx
        exact ⟨⟨i, Nat.lt_succ_of_lt i.isLt⟩,hil,hiu⟩
      · have hn0 : n = 0 := by omega
        subst n
        refine ⟨0, by simpa using hx0, ?_⟩
        norm_num at hx ⊢
        linarith
    · refine ⟨⟨n, Nat.lt_succ_self n⟩, (lt_of_not_ge hx).le, ?_⟩
      simpa only [Fin.val_mk,Nat.cast_add,Nat.cast_one] using hxN

theorem middle_parameter_partition {t : ℝ}
    (htl : (17/20 : ℝ) ≤ t) (htu : t ≤ (9/10 : ℝ)) :
    ∃ i : Fin 50, (850+(i : ℝ))/1000 ≤ t ∧ t ≤ (851+(i : ℝ))/1000 := by
  obtain ⟨i,hil,hiu⟩ := exists_unit_subinterval (by decide : 0 < 50)
    (x := 1000*t-850) (by linarith) (by norm_num; linarith)
  refine ⟨i,?_,?_⟩ <;> linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.middle_parameter_partition
