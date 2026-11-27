import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Real

theorem exists_small_thin_angle_parameter {A η : ℝ} (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧ (3+A/2)*sqrt ε ≤ 1/2 ∧
      2*((3+A/2)*sqrt ε) < η := by
  let C := 3+A/2
  have hC : 0 < C := by dsimp [C]; linarith
  let a := min (1/2 : ℝ) (min (1/(4*C)) (η/(4*C)))
  have ha : 0 < a := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ha1 : a ≤ 1/2 := min_le_left _ _
  have ha2 : a ≤ 1/(4*C) := (min_le_right _ _).trans (min_le_left _ _)
  have ha3 : a ≤ η/(4*C) := (min_le_right _ _).trans (min_le_right _ _)
  have h2 := (le_div_iff₀ (show 0 < 4*C by positivity)).mp ha2
  have h3 := (le_div_iff₀ (show 0 < 4*C by positivity)).mp ha3
  refine ⟨a^2,sq_pos_of_pos ha,by nlinarith,?_,?_⟩
  · rw [sqrt_sq ha.le]
    change C*a ≤ 1/2
    nlinarith
  · rw [sqrt_sq ha.le]
    change 2*(C*a) < η
    nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_small_thin_angle_parameter
