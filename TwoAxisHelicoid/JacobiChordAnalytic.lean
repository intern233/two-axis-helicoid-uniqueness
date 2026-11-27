import TwoAxisHelicoid.JacobiChordGeometry
import TwoAxisHelicoid.JacobiProductAnalytic
import TwoAxisHelicoid.LeftActualPeriod

namespace TwoAxisHelicoid
open Complex Set Metric
set_option maxHeartbeats 800000
attribute [local irreducible] verticalA jacobiPairProduct jacobiProductError

theorem leftNome_lt_one_fifth {t : ℝ} (ht : 0 < t) (htu : t ≤ 17/20) :
    leftNome t < 1/5 := by
  have he : (49/40 : ℝ) < Real.exp (9/40) := by
    linarith [Real.add_one_lt_exp (by norm_num : (9/40 : ℝ) ≠ 0)]
  have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 49/40) (by decide : 8 ≠ 0)
  have he8 : (Real.exp (9/40))^8 = Real.exp (9/5) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he8] at hp
  have h5 : (5 : ℝ) < Real.exp (9/5) := (by norm_num : (5 : ℝ) < (49/40)^8).trans hp
  have hκ : (9/5 : ℝ) < Real.pi/(2*t) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2*t)).mpr
    nlinarith [Real.pi_gt_d2]
  have hlarge := h5.trans (Real.exp_lt_exp.mpr hκ)
  unfold leftNome
  rw [neg_div, Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 5) hlarge

theorem leftNome_lt_one_third {t : ℝ} (ht : 0 < t) (htu : t ≤ 7/5) :
    leftNome t < 1/3 := by
  have he : (207/200 : ℝ) < Real.exp (7/200) := by
    linarith [Real.add_one_lt_exp (by norm_num : (7/200 : ℝ) ≠ 0)]
  have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 207/200) (by decide : 32 ≠ 0)
  have he32 : (Real.exp (7/200))^32 = Real.exp (28/25) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he32] at hp
  have h3 : (3 : ℝ) < Real.exp (28/25) := (by norm_num : (3 : ℝ) < (207/200)^32).trans hp
  have hκ : (28/25 : ℝ) < Real.pi/(2*t) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2*t)).mpr
    nlinarith [Real.pi_gt_d2]
  have hlarge := h3.trans (Real.exp_lt_exp.mpr hκ)
  unfold leftNome
  rw [neg_div, Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3) hlarge

theorem leftChordH_le_one (q : ℝ) : leftChordH q ≤ 1 := by
  have hs := leftChordH_sq_add_K_sq q
  nlinarith [sq_nonneg (leftChordK q), sq_nonneg (leftChordH q-1)]

theorem jacobiChordX_differentiableAt {u : ℂ} (hu : 0 < u.re) :
    DifferentiableAt ℂ jacobiChordX u := by
  exact (differentiableAt_id.add_const I).div
    (differentiableAt_id.sub_const I) (jacobiChord_den_ne_zero hu).1

noncomputable def jacobiChordDifferential (t a : ℝ) (u : ℂ) : ℂ :=
  leftChordDifferential t (dualProductKappa t a) u*
    jacobiProductError (jacobiNome (1/t)) (dualProductR t a) (dualProductKappa t a)
      (jacobiChordX u)

theorem jacobiChordDifferential_differentiableOn {t : ℝ} (ht : 0 < t)
    (hq : leftNome t ≤ 1/3) (a : ℝ) :
    DifferentiableOn ℂ (jacobiChordDifferential t a)
      (ball ((1/leftChordH (leftNome t) : ℝ) : ℂ)
        (1/leftChordH (leftNome t)-leftChordH (leftNome t)/2)) := by
  intro u hu
  have hh := leftChordH_pos (leftNome_pos t)
  have hre := jacobiChord_ball_re hu
  have hu0 : 0 < u.re := by linarith
  have hreg := jacobiChord_ball_product_region (leftNome_pos t) hq hu
  have hQ : ‖jacobiNome (1/t)‖ = (leftNome t)^2 := by
    rw [jacobiNome_inverse_eq_leftNome ht]
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_sq]
  rw [← hQ] at hreg
  have hE := jacobiProductError_differentiableAt (dualProductKappa t a)
    (jacobiNome_norm_lt_one (one_div_pos.mpr ht))
    (show (dualProductR t a : ℂ) ≠ 0 from
      Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    (jacobiChordX_ne_zero hu0) hreg.1 hreg.2
  have hEc := hE.comp u (jacobiChordX_differentiableAt hu0)
  have huI : u ≠ I := by
    intro he
    have h := congrArg Complex.re he
    simp only [I_re] at h
    linarith
  exact ((leftChordDifferential_differentiableAt t (dualProductKappa t a) huI).mul
    hEc).differentiableWithinAt

theorem jacobiChordDifferential_exact_ball {t : ℝ} (ht : 0 < t)
    (hq : leftNome t ≤ 1/3) (a : ℝ) :
    Complex.IsExactOn (jacobiChordDifferential t a)
      (ball ((1/leftChordH (leftNome t) : ℝ) : ℂ)
        (1/leftChordH (leftNome t)-leftChordH (leftNome t)/2)) :=
  (jacobiChordDifferential_differentiableOn ht hq a).isExactOn_ball

theorem leftPathU_mem_jacobiChord_ball {t y : ℝ}
    (hy : y ∈ Icc (-(1/(2*t))) (1/(2*t))) :
    leftPathU y ∈ ball ((1/leftChordH (leftNome t) : ℝ) : ℂ)
      (1/leftChordH (leftNome t)-leftChordH (leftNome t)/2) := by
  rw [leftPathU_eq_arc]
  apply jacobiChord_mem_ball (leftChordH_pos (leftNome_pos t)) (leftChordH_le_one _)
  · exact leftArcPoint_re_lower (leftNome_pos t) (leftPathRho_bounds hy).1 (leftPathRho_bounds hy).2
  · exact (leftArcPoint_norm _).le

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiChordDifferential_exact_ball
