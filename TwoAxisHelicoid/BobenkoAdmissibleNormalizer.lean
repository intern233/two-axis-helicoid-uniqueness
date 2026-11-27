import TwoAxisHelicoid.BobenkoEvenSpinFormula
import TwoAxisHelicoid.BobenkoParameterNormalization

namespace TwoAxisHelicoid
open Set

/-- For every admissible TwoAxisHelicoid parameter the length in Section 6.2 is
uniquely fixed and the actual constant denominator in (38) is nonzero. -/
theorem bobenko_admissible_inverse_and_normalizer {t a : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 1) :
    let L := 1/(2*(1-a))
    1/2 < L ∧ a = 1-1/(2*L) ∧ bobenkoSigmaTwo t L (1/2) ≠ 0 ∧
      ∀ L' : ℝ, a = 1-1/(2*L') → L' = L := by
  intro L
  obtain ⟨hl, formula, unique⟩ := bobenko_admissible_length_inverse ha
  have pos : 0 < L := lt_trans (by norm_num : (0:ℝ)<1/2) hl
  exact ⟨hl, formula, bobenko_sigma_two_normalizer_ne ht pos formula ha, unique⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.bobenko_length_admissible_iff
#print axioms TwoAxisHelicoid.bobenko_admissible_inverse_and_normalizer
