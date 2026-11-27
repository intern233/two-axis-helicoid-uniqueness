import TwoAxisHelicoid.JacobiVerticalIdentity
import TwoAxisHelicoid.RangePeriodBounds

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 400000
attribute [local irreducible] thetaG verticalA jacobiRealE

noncomputable def leftNome (t : ℝ) : ℝ := Real.exp (-Real.pi/(2*t))

theorem leftNome_pos (t : ℝ) : 0 < leftNome t := Real.exp_pos _

theorem leftNome_lt_one {t : ℝ} (ht : 0 < t) : leftNome t < 1 := by
  unfold leftNome
  rw [Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (by positivity)

theorem leftNome_sq {t : ℝ} (ht : 0 < t) :
    (leftNome t)^2 = Real.exp (-Real.pi/t) := by
  unfold leftNome
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  field_simp

theorem thetaG_re_half_pos {t : ℝ} (ht : 0 < t) : 0 < (thetaG t (1/2)).re := by
  rw [thetaG_re_eq_jacobiRealE ht (by norm_num) (by norm_num)]
  have he : Real.exp (-Real.pi*(1/2)/t) = leftNome t := by
    unfold leftNome
    congr 1
    ring
  rw [he, ← leftNome_sq ht]
  exact mul_pos (div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos ht))
    (jacobiRealE_at_q_pos (leftNome_pos t) (leftNome_lt_one ht))

/-- The lower bound in manuscript Lemma 7.2 holds on the whole solvability domain. -/
theorem verticalA_gt_half {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) :
    (1/2 : ℝ) < verticalA t := by
  have ha := verticalA_spec ht
  have hg := thetaG_re_half_pos ht.1
  by_contra hn
  have hm := (thetaG_strictAnti_unit_of_pos ht.1).antitoneOn ha.1
    (by norm_num : (1/2 : ℝ) ∈ Ioo (0 : ℝ) 1) (le_of_not_gt hn)
  change (thetaG t (1/2)).re ≤ (thetaG t (verticalA t)).re at hm
  rw [ha.2] at hm
  norm_num at hm
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaG_re_half_pos
#print axioms TwoAxisHelicoid.verticalA_gt_half
