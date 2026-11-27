import TwoAxisHelicoid.VerticalHalfLowerBound
import TwoAxisHelicoid.JacobiSmallRootBounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 800000
attribute [local irreducible] thetaG verticalA jacobiRealE

theorem leftNome_lt_one_hundredth {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    leftNome t < 1/100 := by
  have harg : -Real.pi/(2*t) < -6 := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*t)).mpr
    nlinarith [Real.pi_gt_three]
  have hbase : (5/2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow := pow_lt_pow_left₀ hbase (by norm_num : (0 : ℝ) ≤ 5/2) (by decide : 6 ≠ 0)
  have he : (Real.exp 1)^6 = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
  have hlarge : (100 : ℝ) < Real.exp 6 := by rw [he] at hpow; norm_num at hpow; linarith
  have hbound : Real.exp (-6) < 1/100 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num) hlarge
  exact (Real.exp_lt_exp.mpr harg).trans hbound

noncomputable def smallVerticalUpper (t : ℝ) : ℝ := 1/2+(t/Real.pi)*Real.log 2

theorem smallVerticalUpper_mem_unit {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    smallVerticalUpper t ∈ Ioo (0 : ℝ) 1 := by
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).mpr Real.exp_one_gt_two
  have hratio0 := div_pos ht Real.pi_pos
  have hratio : t/Real.pi < (1/2 : ℝ) := by
    apply (div_lt_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  have hm := mul_lt_of_lt_one_right hratio0 hlog1
  unfold smallVerticalUpper
  constructor
  · positivity
  · linarith

theorem exp_smallVerticalUpper {t : ℝ} (ht : 0 < t) :
    Real.exp (-Real.pi*smallVerticalUpper t/t) = leftNome t/2 := by
  have he : -Real.pi*smallVerticalUpper t/t = -Real.pi/(2*t)-Real.log 2 := by
    unfold smallVerticalUpper
    field_simp [ht.ne', Real.pi_ne_zero]
    ring
  rw [he, Real.exp_sub, Real.exp_log (by norm_num)]
  rfl

theorem thetaG_re_smallVerticalUpper_neg {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    (thetaG t (smallVerticalUpper t)).re < 0 := by
  have ha := smallVerticalUpper_mem_unit ht htu
  rw [thetaG_re_eq_jacobiRealE ht ha.1 ha.2, exp_smallVerticalUpper ht, ← leftNome_sq ht]
  exact mul_neg_of_pos_of_neg (div_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos ht))
    ((jacobiRealE_half_q_lt_neg_q (leftNome_pos t) (leftNome_lt_one_hundredth ht htu).le).trans
      (neg_neg_of_pos (leftNome_pos t)))

theorem small_height_mem_vertical_domain {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    t ∈ Ioo (0 : ℝ) ellipticVerticalUpper :=
  ⟨ht, htu.trans_lt ((by norm_num : (1/4 : ℝ) < 100000000/70945980).trans
    ellipticVerticalUpper_location.1)⟩

/-- Both bounds in manuscript Lemma 7.2 for the actual vertical branch. -/
theorem verticalA_small_bounds {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    (1/2 : ℝ) < verticalA t ∧ verticalA t < 1/2+(t/Real.pi)*Real.log 2 := by
  have hdomain := small_height_mem_vertical_domain ht htu
  have ha := verticalA_spec hdomain
  have hu := smallVerticalUpper_mem_unit ht htu
  have hg := thetaG_re_smallVerticalUpper_neg ht htu
  refine ⟨verticalA_gt_half hdomain, ?_⟩
  change verticalA t < smallVerticalUpper t
  by_contra hn
  have hm := (thetaG_strictAnti_unit_of_pos ht).antitoneOn hu ha.1 (le_of_not_gt hn)
  change (thetaG t (verticalA t)).re ≤ (thetaG t (smallVerticalUpper t)).re at hm
  rw [ha.2] at hm
  norm_num at hm
  linarith

theorem exp_verticalA_small_bounds {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/4) :
    leftNome t/2 < Real.exp (-Real.pi*verticalA t/t) ∧
      Real.exp (-Real.pi*verticalA t/t) < leftNome t := by
  have ha := verticalA_small_bounds ht htu
  constructor
  · rw [← exp_smallVerticalUpper ht]
    apply Real.exp_lt_exp.mpr
    apply (div_lt_div_iff_of_pos_right ht).mpr
    exact mul_lt_mul_of_neg_left ha.2 (neg_neg_of_pos Real.pi_pos)
  · have he : leftNome t = Real.exp (-Real.pi*(1/2)/t) := by
      unfold leftNome
      congr 1
      ring
    rw [he]
    apply Real.exp_lt_exp.mpr
    apply (div_lt_div_iff_of_pos_right ht).mpr
    exact mul_lt_mul_of_neg_left ha.1 (neg_neg_of_pos Real.pi_pos)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.verticalA_small_bounds
#print axioms TwoAxisHelicoid.exp_verticalA_small_bounds
