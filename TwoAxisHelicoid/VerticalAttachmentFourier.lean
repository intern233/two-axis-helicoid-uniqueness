import TwoAxisHelicoid.VerticalAttachmentNome
import TwoAxisHelicoid.VerticalRunCoreAgreement
import TwoAxisHelicoid.VerticalSeries

namespace TwoAxisHelicoid.VerticalAttachment

private theorem real_series_cut (x : ℚ) :
    ((VerticalRunCore.seriesCut x : ℚ) : ℝ) =
      ∑ i ∈ Finset.range 40, (fourierCoefficientAt (i+1) : ℝ)*(x : ℝ)^(i+1) := by
  simp [VerticalRun.core_series_cut_eq, Rat.cast_sum]

private theorem real_series_tail (x : ℚ) :
    ((VerticalRunCore.seriesTail x : ℚ) : ℝ) = squareTail (x : ℝ) 40 := by
  norm_num [VerticalRunCore.seriesTail, squareTail]

/-- The attachment's 40-term rational calculation encloses the infinite Fourier series
at every input for which its rounded nome stays in the interval of convergence. -/
theorem normalized_F_algorithm_contains {t : ℚ} (ht : 0 < t)
    (harg : piBox.2*t ≤ 61) (hl : 0 ≤ (nome piBox t t).1)
    (hu : (nome piBox t t).2 < 1) :
    ContainsReal (normalizedF t) (verticalSeries (t : ℝ)/Real.pi^2) := by
  let b := nome piBox t t
  let x := Real.exp (-Real.pi*(t : ℝ))
  have h : ContainsReal b x := by
    simpa only [b, x, neg_mul] using uploaded_nome_contains ht.le le_rfl le_rfl harg
  have l : 0 ≤ (b.1 : ℝ) := by
    change 0 ≤ ((nome piBox t t).1 : ℝ)
    exact_mod_cast hl
  have u : (b.2 : ℝ) < 1 := by
    change ((nome piBox t t).2 : ℝ) < 1
    exact_mod_cast hu
  have xm := vertical_nome_mem (show 0 < (t : ℝ) by exact_mod_cast ht)
  have low := (qSeries_partial_sum_bounds l (h.1.trans_lt xm.2) 40).1.trans
    (qSeries_strictMonoOn.monotoneOn ⟨l, h.1.trans_lt xm.2⟩ ⟨xm.1.le, xm.2⟩ h.1)
  have high := (qSeries_strictMonoOn.monotoneOn ⟨xm.1.le, xm.2⟩
    ⟨xm.1.le.trans h.2, u⟩ h.2).trans (qSeries_partial_sum_bounds (xm.1.le.trans h.2) u 40).2
  have formula : verticalSeries (t : ℝ)/Real.pi^2 = 1/4-2*qSeries x := by
    rw [verticalSeries_eq_qSeries]
    dsimp only [x]
    rw [neg_mul]
    field_simp [Real.pi_ne_zero]
  change (((1/4-2*(VerticalRunCore.seriesCut b.2+VerticalRunCore.seriesTail b.2) : ℚ) : ℝ) ≤ _) ∧
    _ ≤ ((1/4-2*VerticalRunCore.seriesCut b.1 : ℚ) : ℝ)
  simp only [formula, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat, real_series_cut, real_series_tail]
  constructor <;> linarith

theorem original_point_Fourier_enclosures :
    ContainsReal (normalizedF left) (verticalSeries (left : ℝ)/Real.pi^2) ∧
    ContainsReal (normalizedF right) (verticalSeries (right : ℝ)/Real.pi^2) := by
  constructor
  · exact normalized_F_algorithm_contains (by decide +kernel) (by rw [original_pi_box]; decide +kernel)
      (by rw [original_left_nome]; decide +kernel) (by rw [original_left_nome]; decide +kernel)
  · exact normalized_F_algorithm_contains (by decide +kernel) (by rw [original_pi_box]; decide +kernel)
      (by rw [original_right_nome]; decide +kernel) (by rw [original_right_nome]; decide +kernel)

end TwoAxisHelicoid.VerticalAttachment

#print axioms TwoAxisHelicoid.VerticalAttachment.normalized_F_algorithm_contains
#print axioms TwoAxisHelicoid.VerticalAttachment.original_point_Fourier_enclosures
