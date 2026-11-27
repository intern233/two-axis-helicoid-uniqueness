import TwoAxisHelicoid.HalfThetaF

namespace TwoAxisHelicoid

theorem ellipticNome_le_hundredth {t : ℝ} (ht : 2 ≤ t) : ellipticNome t ≤ 1/100 := by
  have harg : (6:ℝ) ≤ Real.pi*t := by nlinarith [Real.pi_gt_three]
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 6) 5
  norm_num [Finset.sum_range_succ] at he
  have hexp : (100:ℝ) ≤ Real.exp (Real.pi*t) :=
    le_trans (by linarith) (Real.exp_le_exp.mpr harg)
  unfold ellipticNome
  rw [show -Real.pi*t = -(Real.pi*t) by ring,Real.exp_neg]
  rw [← one_div,div_le_iff₀ (Real.exp_pos _)]
  nlinarith

theorem halfThetaB_div_A_gt_nine_tenths {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1/100) :
    9/10 < halfThetaSum halfWeightB q/halfThetaSum halfWeightA q := by
  have hq4 : q ≤ 1/4 := by linarith
  have ha := halfThetaSum_A_pos hq0 hq4
  have hr := halfTheta_remainder_bounds hq0 hq4
  have hA := (abs_le.mp hr.1).2
  have hB := (abs_le.mp hr.2.1).1
  have hq3 : q^3 ≤ (1/100:ℝ)^3 := pow_le_pow_left₀ hq0 hq 3
  rw [lt_div_iff₀ ha]
  nlinarith

theorem ellipticFReal_gt_two {t : ℝ} (ht : 2 ≤ t) : 2 < ellipticFReal t := by
  have hq := halfThetaB_div_A_gt_nine_tenths (ellipticNome_pos t).le
    (ellipticNome_le_hundredth ht)
  have hp : (9:ℝ) < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  rw [ellipticFReal_formula,mul_div_assoc]
  nlinarith

theorem ellipticFReal_reciprocal {t : ℝ} (ht : 0 < t) :
    ellipticFReal t = Real.pi/t-ellipticFReal (1/t)/t^2 := by
  simpa only [ellipticF_eq_ellipticFReal] using ellipticF_reciprocal ht

theorem ellipticFReal_neg_of_small {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1/2) :
    ellipticFReal t < 0 := by
  have hi : 2 ≤ 1/t := (le_div_iff₀ ht).mpr (by linarith)
  have hF := ellipticFReal_gt_two hi
  have hpi : Real.pi*t < 2 := by nlinarith [Real.pi_lt_four]
  rw [ellipticFReal_reciprocal ht]
  have he : Real.pi/t-ellipticFReal (1/t)/t^2 =
      (Real.pi*t-ellipticFReal (1/t))/t^2 := by field_simp
  rw [he]
  exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos ht)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.ellipticFReal_neg_of_small
