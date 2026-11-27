import Mathlib.Tactic

namespace TwoAxisHelicoid

/-- Adjacent intervals cover the interval between the first and last endpoint.
No floating-point comparison or assumption about a generated partition is used. -/
theorem exists_adjacent_interval (n : ℕ) (b : ℕ → ℝ) {x : ℝ}
    (hl : b 0 ≤ x) (hu : x ≤ b (n+1)) :
    ∃ i : Fin (n+1), b i ≤ x ∧ x ≤ b (i+1) := by
  induction n with
  | zero => exact ⟨0,hl,hu⟩
  | succ n ih =>
    by_cases hx : x ≤ b (n+1)
    · obtain ⟨i,hil,hiu⟩ := ih hx
      exact ⟨i.castSucc,hil,hiu⟩
    · exact ⟨Fin.last (n+1),(lt_of_not_ge hx).le,hu⟩

theorem predicate_on_interval_chain (n : ℕ) (b : ℕ → ℝ) (P : ℝ → Prop)
    (hP : ∀ i : Fin (n+1), ∀ x, b i ≤ x → x ≤ b (i+1) → P x)
    {x : ℝ} (hl : b 0 ≤ x) (hu : x ≤ b (n+1)) : P x := by
  obtain ⟨i,hil,hiu⟩ := exists_adjacent_interval n b hl hu
  exact hP i x hil hiu

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.predicate_on_interval_chain
