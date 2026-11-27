import TwoAxisHelicoid.FlatHolomorphicSections
import TwoAxisHelicoid.SpinorMultipliers
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Parity

namespace TwoAxisHelicoid

theorem integerSpinorSections_finrank {t : ℝ} (ht : 0 < t) (m : ℤ) :
    Module.finrank ℂ (flatHolomorphicSections t 1 ((-1 : ℂ)^m)) = if Even m then 1 else 0 := by
  classical
  by_cases hm : Even m
  · rw [ite_eq_left hm,hm.neg_one_zpow]
    exact trivialFlatSections_finrank ht
  · rw [ite_eq_right hm,neg_one_zpow_eq_ite,ite_eq_right hm]
    exact nontrivialFlatSections_finrank ht (by norm_num) (by norm_num) (Or.inr (by norm_num))

/-- Parity of the dimension of holomorphic equivariant sections of the
actual flat multiplier system. The spatially induced spin structure still
has to be identified with this system before applying it to a surface. -/
theorem integerSpinorSections_even_iff_odd_parameter {t : ℝ} (ht : 0 < t) (m : ℤ) :
    Even (Module.finrank ℂ (flatHolomorphicSections t 1 ((-1 : ℂ)^m))) ↔ Odd m := by
  classical
  rw [integerSpinorSections_finrank ht m]
  by_cases hm : Even m
  · simp [hm,← Int.not_even_iff_odd]
  · simp [hm,← Int.not_even_iff_odd]

theorem integerSpinor_basic_parameter {t : ℝ} (ht : 0 < t) (m : ℤ)
    (hbound : m = 0 ∨ m = 1)
    (hparity : Even (Module.finrank ℂ (flatHolomorphicSections t 1 ((-1 : ℂ)^m)))) : m = 1 := by
  have hm := (integerSpinorSections_even_iff_odd_parameter ht m).mp hparity
  rcases hbound with rfl | he
  · norm_num at hm
  · exact he

noncomputable def integerSpinCharacter (m : ℤ) (p : ℤ × ℤ) : ℂ := (-1 : ℂ)^(m*p.2)

theorem integerSpinCharacter_add (m : ℤ) (p q : ℤ × ℤ) :
    integerSpinCharacter m (p+q) = integerSpinCharacter m p*integerSpinCharacter m q := by
  unfold integerSpinCharacter
  simp only [Prod.snd_add,mul_add]
  exact zpow_add₀ (by norm_num) _ _

theorem integerSpinCharacter_sq (m : ℤ) (p : ℤ × ℤ) : (integerSpinCharacter m p)^2 = 1 := by
  unfold integerSpinCharacter
  rw [neg_one_zpow_eq_ite]
  split_ifs <;> norm_num

theorem integerSpinCharacter_generators (m : ℤ) :
    integerSpinCharacter m (1,0) = 1 ∧ integerSpinCharacter m (0,1) = (-1 : ℂ)^m := by
  simp [integerSpinCharacter]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.integerSpinorSections_even_iff_odd_parameter
#print axioms TwoAxisHelicoid.integerSpinCharacter_add
