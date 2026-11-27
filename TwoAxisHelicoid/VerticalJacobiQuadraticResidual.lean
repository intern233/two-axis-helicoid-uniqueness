import TwoAxisHelicoid.JacobiRootAsymptotic
import Mathlib.Analysis.Asymptotics.Lemmas

namespace TwoAxisHelicoid
open Set Filter Asymptotics
open scoped Topology
attribute [local irreducible] verticalA jacobiRealE

/-- The first quadratic balance in Appendix B.1, directly on the vertical
root, before replacing the sum of squares by twice the squared nome. -/
theorem left_actual_root_quadratic_residual_bound {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    |leftRootR t-leftBeta t+2*((leftRootR t)^2+(leftBeta t)^2)| ≤ 40*(leftNome t)^3 := by
  let q := leftNome t
  let r := leftRootR t
  let b := leftBeta t
  have q0 : 0 < q := leftNome_pos t
  have qu : q ≤ 1/100 := (leftNome_lt_one_hundredth ht htu).le
  have r0 : 0 < r := leftRootR_pos t
  have b0 : 0 < b := leftBeta_pos t
  have ru : r ≤ q := (leftRootR_bounds ht htu).2.le
  have rl : q/2 ≤ r := (leftRootR_bounds ht htu).1.le
  have bu : b ≤ 2*q := (leftBeta_bounds ht htu).2
  have he := jacobiRealE_split_root q0 qu rl ru
  rw [jacobiRealE_at_verticalA_zero (small_height_mem_vertical_domain ht htu)] at he
  change 0 = jacobiFraction r-b/(1+b)^2+jacobiRootRemainder q r at he
  have negfrac : jacobiFraction (-b) = -b/(1+b)^2 := by
    unfold jacobiFraction
    congr 1
    ring
  have split : b-r-2*(r^2+b^2) =
      (jacobiFraction r-r-2*r^2)+(jacobiFraction (-b)+b-2*b^2)+jacobiRootRemainder q r := by
    rw [negfrac]
    linear_combination he
  have er := jacobiFraction_second_remainder (x := r) (by rw [abs_of_pos r0]; linarith)
  have eb := jacobiFraction_second_remainder (x := -b) (by rw [abs_neg,abs_of_pos b0]; linarith)
  simp only [sub_neg_eq_add, neg_sq, abs_neg, abs_of_pos b0] at eb
  rw [abs_of_pos r0] at er
  have tail := (jacobiRootRemainder_abs_lt q0 qu rl ru).le
  have r3 := pow_le_pow_left₀ r0.le ru 3
  have b3 := pow_le_pow_left₀ b0.le bu 3
  change |r-b+2*(r^2+b^2)| ≤ 40*q^3
  rw [show r-b+2*(r^2+b^2) = -(b-r-2*(r^2+b^2)) by ring, abs_neg, split]
  have triangle := (abs_add_le
      ((jacobiFraction r-r-2*r^2)+(jacobiFraction (-b)+b-2*b^2)) (jacobiRootRemainder q r)).trans
    (add_le_add (abs_add_le (jacobiFraction r-r-2*r^2) (jacobiFraction (-b)+b-2*b^2))
      (le_refl |jacobiRootRemainder q r|))
  nlinarith only [triangle,er,eb,tail,r3,b3]

theorem left_actual_root_quadratic_residual_isBigO :
    (fun t : ℝ => leftRootR t-leftBeta t+2*((leftRootR t)^2+(leftBeta t)^2))
      =O[𝓝[>] (0:ℝ)] (fun t => (leftNome t)^3) := by
  apply isBigO_iff.mpr
  refine ⟨40,?_⟩
  have upper : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1/4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, upper] with t positive small
  simpa only [Real.norm_eq_abs, abs_of_pos (pow_pos (leftNome_pos t) 3)] using
    left_actual_root_quadratic_residual_bound (show 0 < t from positive) small.le

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_actual_root_quadratic_residual_bound
#print axioms TwoAxisHelicoid.left_actual_root_quadratic_residual_isBigO
