module

public import TwoAxisHelicoid.VerticalAttachmentPi
import all TwoAxisHelicoid.VerticalDecimalBoxes
public import TwoAxisHelicoid.VerticalTaylorBounds

public section

namespace TwoAxisHelicoid.VerticalAttachment

private theorem factorial_eq (n : ℕ) : VerticalRunCore.factorial n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VerticalRunCore.factorial, ih, Nat.factorial_succ]

private theorem cast_taylor (x : ℚ) (n : ℕ) :
    ((taylor x n : ℚ) : ℝ) = expPartial (x : ℝ) n := by
  simp [taylor, sumPrefix_cast_real, factorial_eq, expPartial]

/-- Exact real-number semantics of the exponential interval routine on its input range. -/
theorem uploaded_exponential_contains {lo hi : ℚ} {x : ℝ}
    (h0 : 0 ≤ lo) (h61 : hi ≤ 61) (hl : (lo : ℝ) ≤ x) (hu : x ≤ (hi : ℝ)) :
    ContainsReal (exponential lo hi) (Real.exp (-x)) := by
  have l0 : 0 ≤ (lo : ℝ) := by exact_mod_cast h0
  have u61 : (hi : ℝ) ≤ 61 := by exact_mod_cast h61
  apply outward_contains_real
  · rw [cast_taylor]
    exact (expPartial_bounds (l0.trans (hl.trans hu)) u61).1.trans
      (Real.exp_le_exp.mpr (neg_le_neg hu))
  · rw [cast_taylor]
    exact (Real.exp_le_exp.mpr (neg_le_neg hl)).trans
      (expPartial_bounds l0 ((hl.trans hu).trans u61)).2

theorem uploaded_nome_contains {lo hi : ℚ} {t : ℝ}
    (h0 : 0 ≤ lo) (hl : (lo : ℝ) ≤ t) (hu : t ≤ (hi : ℝ)) (h61 : piBox.2 * hi ≤ 61) :
    ContainsReal (nome piBox lo hi) (Real.exp (-(Real.pi*t))) := by
  have p0 : 0 ≤ piBox.1 := by rw [original_pi_box]; decide +kernel
  have t0 : 0 ≤ t := (show 0 ≤ (lo : ℝ) by exact_mod_cast h0).trans hl
  apply uploaded_exponential_contains (mul_nonneg p0 h0) h61
  · rw [Rat.cast_mul]
    exact mul_le_mul uploaded_machin_pi_contains.1 hl (by exact_mod_cast h0) Real.pi_pos.le
  · rw [Rat.cast_mul]
    exact mul_le_mul uploaded_machin_pi_contains.2 hu t0
      (Real.pi_pos.le.trans uploaded_machin_pi_contains.2)

/-- Both point nomes and the full reciprocal endpoint box in the uploaded run. -/
theorem original_three_nome_enclosures :
    ContainsReal leftNome (Real.exp (-(Real.pi*(left : ℝ)))) ∧
    ContainsReal rightNome (Real.exp (-(Real.pi*(right : ℝ)))) ∧
    ∀ t : ℝ, ((1/right : ℚ) : ℝ) ≤ t → t ≤ ((1/left : ℚ) : ℝ) →
      ContainsReal endpointNome (Real.exp (-(Real.pi*t))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← original_left_nome]
    exact uploaded_nome_contains (by decide +kernel) le_rfl le_rfl (by rw [original_pi_box]; decide +kernel)
  · rw [← original_right_nome]
    exact uploaded_nome_contains (by decide +kernel) le_rfl le_rfl (by rw [original_pi_box]; decide +kernel)
  · intro t hl hu
    rw [← original_endpoint_nome]
    exact uploaded_nome_contains (by decide +kernel) hl hu (by rw [original_pi_box]; decide +kernel)

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.uploaded_exponential_contains
#print axioms TwoAxisHelicoid.VerticalAttachment.original_three_nome_enclosures
