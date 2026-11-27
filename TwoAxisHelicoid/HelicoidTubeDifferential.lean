import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TwoAxisHelicoid
open Real Set

noncomputable def helicoidQ (r : ℝ) : ℝ := √(1+r^2)
noncomputable def helicoidAngle (r s : ℝ) : ℝ := s*r/helicoidQ r
noncomputable def helicoidU (r s : ℝ) : ℝ :=
  r*cos (helicoidAngle r s) - s/helicoidQ r*sin (helicoidAngle r s)
noncomputable def helicoidV (r s : ℝ) : ℝ :=
  -r*sin (helicoidAngle r s) - s/helicoidQ r*cos (helicoidAngle r s)
noncomputable def helicoidA (r s : ℝ) : ℝ := 1-s^2/(helicoidQ r)^4
noncomputable def helicoidUr (r s : ℝ) : ℝ := helicoidA r s*cos (helicoidAngle r s)
noncomputable def helicoidVr (r s : ℝ) : ℝ := -helicoidA r s*sin (helicoidAngle r s)
noncomputable def helicoidUs (r s : ℝ) : ℝ :=
  -(s*r/(helicoidQ r)^2)*cos (helicoidAngle r s)-helicoidQ r*sin (helicoidAngle r s)
noncomputable def helicoidVs (r s : ℝ) : ℝ :=
  (s*r/(helicoidQ r)^2)*sin (helicoidAngle r s)-helicoidQ r*cos (helicoidAngle r s)

theorem helicoidQ_pos (r : ℝ) : 0 < helicoidQ r := by
  exact sqrt_pos.mpr (by positivity)

theorem helicoidQ_sq (r : ℝ) : (helicoidQ r)^2 = 1+r^2 := by
  exact sq_sqrt (by positivity)

theorem helicoidQ_ge_one (r : ℝ) : 1 ≤ helicoidQ r := by
  nlinarith [helicoidQ_sq r,helicoidQ_pos r,sq_nonneg r]

theorem helicoidQ_hasDerivAt (r : ℝ) : HasDerivAt helicoidQ (r/helicoidQ r) r := by
  have h := ((hasDerivAt_const r (1:ℝ)).add ((hasDerivAt_id r).pow 2)).sqrt
    (show 1+r^2 ≠ 0 by positivity)
  convert h using 1
  · rfl
  · simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    unfold helicoidQ
    ring

theorem helicoidAngle_r_hasDerivAt (r s : ℝ) :
    HasDerivAt (fun x => helicoidAngle x s) (s/(helicoidQ r)^3) r := by
  have h := ((hasDerivAt_id r).const_mul s).div (helicoidQ_hasDerivAt r) (helicoidQ_pos r).ne'
  convert h using 1
  · rfl
  · have hq := helicoidQ_sq r
    simp only [id_eq]
    field_simp [(helicoidQ_pos r).ne']
    rw [hq]
    ring

theorem helicoidAngle_s_hasDerivAt (r s : ℝ) :
    HasDerivAt (helicoidAngle r) (r/helicoidQ r) s := by
  change HasDerivAt (fun x : ℝ => x*r/helicoidQ r) (r/helicoidQ r) s
  simpa only [one_mul, id_eq] using ((hasDerivAt_id s).mul_const r).div_const (helicoidQ r)

theorem helicoidU_r_hasDerivAt (r s : ℝ) :
    HasDerivAt (fun x => helicoidU x s) (helicoidUr r s) r := by
  have ha := helicoidAngle_r_hasDerivAt r s
  have hb := (hasDerivAt_const r s).div (helicoidQ_hasDerivAt r) (helicoidQ_pos r).ne'
  have h := ((hasDerivAt_id r).mul ha.cos).sub (hb.mul ha.sin)
  convert h using 1
  · rfl
  · unfold helicoidUr helicoidA
    simp only [id_eq, Pi.div_apply]
    field_simp [(helicoidQ_pos r).ne']
    ring

theorem helicoidV_r_hasDerivAt (r s : ℝ) :
    HasDerivAt (fun x => helicoidV x s) (helicoidVr r s) r := by
  have ha := helicoidAngle_r_hasDerivAt r s
  have hb := (hasDerivAt_const r s).div (helicoidQ_hasDerivAt r) (helicoidQ_pos r).ne'
  have h := ((hasDerivAt_id r).neg.mul ha.sin).sub (hb.mul ha.cos)
  convert h using 1
  · rfl
  · unfold helicoidVr helicoidA
    simp only [id_eq, Pi.div_apply, Pi.neg_apply]
    field_simp [(helicoidQ_pos r).ne']
    ring

theorem helicoidU_s_hasDerivAt (r s : ℝ) :
    HasDerivAt (helicoidU r) (helicoidUs r s) s := by
  have ha := helicoidAngle_s_hasDerivAt r s
  have h := (ha.cos.const_mul r).sub (((hasDerivAt_id s).div_const (helicoidQ r)).mul ha.sin)
  convert h using 1
  · rfl
  · unfold helicoidUs
    have hq := helicoidQ_sq r
    simp only [id_eq]
    field_simp [(helicoidQ_pos r).ne']
    nlinarith [congrArg (fun x : ℝ => x*helicoidQ r*sin (helicoidAngle r s)) hq]

theorem helicoidV_s_hasDerivAt (r s : ℝ) :
    HasDerivAt (helicoidV r) (helicoidVs r s) s := by
  have ha := helicoidAngle_s_hasDerivAt r s
  have h := (ha.sin.const_mul (-r)).sub (((hasDerivAt_id s).div_const (helicoidQ r)).mul ha.cos)
  convert h using 1
  · rfl
  · unfold helicoidVs
    have hq := helicoidQ_sq r
    simp only [id_eq]
    field_simp [(helicoidQ_pos r).ne']
    nlinarith [congrArg (fun x : ℝ => x*helicoidQ r*cos (helicoidAngle r s)) hq]

theorem helicoid_jacobian (r s : ℝ) :
    helicoidUr r s*helicoidVs r s-helicoidUs r s*helicoidVr r s =
      -helicoidQ r*helicoidA r s := by
  unfold helicoidUr helicoidVs helicoidUs helicoidVr
  calc
    _ = -helicoidQ r*helicoidA r s*(sin (helicoidAngle r s)^2+cos (helicoidAngle r s)^2) := by ring
    _ = _ := by rw [sin_sq_add_cos_sq, mul_one]

theorem helicoidAngle_sq_lt_one (r s : ℝ) (hs : |s| < 1) :
    (helicoidAngle r s)^2 < 1 := by
  have hq := helicoidQ_pos r
  have hq2 := helicoidQ_sq r
  have hs2 : s^2 < 1 := (sq_lt_one_iff_abs_lt_one s).mpr hs
  unfold helicoidAngle
  rw [div_pow,div_lt_one (sq_pos_of_pos hq)]
  nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hs2)) (sq_nonneg r)]

theorem helicoidA_lower (r s : ℝ) (_hs : |s| < 1) : 1-s^2 ≤ helicoidA r s := by
  have hq := helicoidQ_ge_one r
  have hq4 : 1 ≤ (helicoidQ r)^4 := one_le_pow₀ hq
  unfold helicoidA
  have hdiv : s^2/(helicoidQ r)^4 ≤ s^2 := div_le_self (sq_nonneg s) hq4
  linarith

theorem helicoidUr_lower (r s : ℝ) (hs : |s| < 1) :
    (1-s^2)/2 ≤ helicoidUr r s := by
  have hs2 : s^2 < 1 := (sq_lt_one_iff_abs_lt_one s).mpr hs
  have hc : (1:ℝ)/2 ≤ cos (helicoidAngle r s) := by
    nlinarith [one_sub_sq_div_two_le_cos (x := helicoidAngle r s),helicoidAngle_sq_lt_one r s hs]
  have hA := helicoidA_lower r s hs
  unfold helicoidUr
  nlinarith [mul_nonneg (sub_nonneg.mpr hA) (le_trans (by norm_num) hc),
    mul_nonneg (sub_nonneg.mpr hc) (le_of_lt (sub_pos.mpr hs2))]

theorem helicoidUr_pos (r s : ℝ) (hs : |s| < 1) : 0 < helicoidUr r s := by
  have hs2 : s^2 < 1 := (sq_lt_one_iff_abs_lt_one s).mpr hs
  linarith [helicoidUr_lower r s hs]

theorem helicoid_jacobian_neg (r s : ℝ) (hs : |s| < 1) :
    helicoidUr r s*helicoidVs r s-helicoidUs r s*helicoidVr r s < 0 := by
  rw [helicoid_jacobian]
  have hs2 : s^2 < 1 := (sq_lt_one_iff_abs_lt_one s).mpr hs
  have hA : 0 < helicoidA r s := by linarith [helicoidA_lower r s hs]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (helicoidQ_pos r)) hA

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.helicoidU_r_hasDerivAt
#print axioms TwoAxisHelicoid.helicoid_jacobian_neg
