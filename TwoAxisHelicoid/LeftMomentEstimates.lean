import TwoAxisHelicoid.LeftComparisonPath
import TwoAxisHelicoid.LeftNumericalConstants
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/- Integral estimates for the actual small-height period. -/

/- LeftComparisonNorm -/

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
set_option maxHeartbeats 800000
attribute [local irreducible] verticalA

noncomputable def leftMomentDensity (κ ρ : ℝ) : ℝ :=
  (ρ/(1+ρ^2))*Real.exp (κ*((1-ρ^2)/(1+ρ^2)))

noncomputable def leftErrorMoment (t : ℝ) (j : ℕ) : ℝ :=
  ∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)),
    ‖leftComparisonFunction t (leftPathW y)‖*(leftProductB t (Real.exp (-Real.pi*y)))^j

theorem norm_one_sub_I_real_sq (ρ : ℝ) : ‖(1 : ℂ)-I*(ρ : ℂ)‖^2 = 1+ρ^2 := by
  rw [Complex.sq_norm, normSq_apply]
  simp only [sub_re, sub_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
    one_re, one_im, zero_mul, mul_zero, one_mul, zero_add, sub_zero, zero_sub]
  ring

theorem re_main_exponent (κ ρ : ℝ) :
    ((κ : ℂ)*(-1+2/(1-I*(ρ : ℂ)))).re = κ*((1-ρ^2)/(1+ρ^2)) := by
  have hd : (1+ρ^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  simp only [mul_re, mul_im, add_re, sub_re, sub_im, div_re, ofReal_re, ofReal_im,
    I_re, I_im, one_re, one_im, neg_re, re_ofNat, im_ofNat, normSq_apply,
    zero_mul, mul_zero, one_mul, zero_add, sub_zero, zero_sub]
  field_simp [hd]
  ring

theorem leftComparison_norm {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ‖leftComparisonFunction t (leftPathW y)‖ =
      (Real.pi^2/t)*(Real.exp (-Real.pi*y))*
        leftMomentDensity (leftKappa t) (Real.exp (-Real.pi*y)) := by
  unfold leftComparisonFunction dualProductMainTerm leftPathW
  rw [jacobiExp_half_midline, ← leftKappa_eq_dualProductKappa ht]
  simp only [norm_mul, norm_div, norm_pow, norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht, abs_of_pos Real.pi_pos, abs_of_pos (Real.exp_pos _),
    Complex.norm_exp, re_main_exponent]
  unfold leftMomentDensity
  field_simp [ht.ne']
  rw [norm_one_sub_I_real_sq]
  exact div_self (ne_of_gt (by positivity))

theorem leftMomentDensity_continuous (κ : ℝ) : Continuous (leftMomentDensity κ) := by
  unfold leftMomentDensity
  have hd (ρ : ℝ) : 1+ρ^2 ≠ 0 := ne_of_gt (by positivity)
  fun_prop (disch := exact hd _)

theorem leftProductB_continuousAt (t : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ContinuousAt (leftProductB t) ρ := by
  unfold leftProductB
  fun_prop (disch := exact hρ)

theorem leftErrorMoment_integrable (t : ℝ) (j : ℕ) :
    IntervalIntegrable (fun y : ℝ => ‖leftComparisonFunction t (leftPathW y)‖*
      (leftProductB t (Real.exp (-Real.pi*y)))^j) volume (-(1/(2*t))) (1/(2*t)) := by
  have hc : Continuous (fun y : ℝ => leftComparisonFunction t (leftPathW y)) := by
    have h := leftComparison_path_continuous t
    have he : (fun y => leftComparisonFunction t (leftPathW y)) =
        (fun y => (-I)*(I*leftComparisonFunction t (leftPathW y))) := by
      funext y
      have hi : (-I)*I = (1 : ℂ) := by
        calc
          _ = -(I^2) := by ring
          _ = 1 := by rw [I_sq]; norm_num
      rw [← mul_assoc, hi, one_mul]
    rw [he]
    exact continuous_const.mul h
  have hB : Continuous (fun y : ℝ => leftProductB t (Real.exp (-Real.pi*y))) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (leftProductB_continuousAt t (Real.exp_ne_zero (-Real.pi*y))).comp
      (f := fun x : ℝ => Real.exp (-Real.pi*x)) (by fun_prop)
  exact (hc.norm.mul (hB.pow j)).intervalIntegrable _ _

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftComparison_norm

/- LeftMomentConstants -/

namespace TwoAxisHelicoid
open Set
set_option maxHeartbeats 800000

theorem leftBeta_mul_exp_kappa (t : ℝ) : leftBeta t*Real.exp (leftKappa t) = 1 := by
  rw [← exp_neg_leftKappa, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem leftRootR_le_beta {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftRootR t ≤ leftBeta t :=
  (leftRootR_bounds ht (by linarith)).2.le.trans (leftBeta_bounds ht (by linarith)).1

theorem leftNome_mul_exp_kappa_le_one {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftNome t*Real.exp (leftKappa t) ≤ 1 := by
  have hm := mul_le_mul_of_nonneg_right (leftBeta_bounds ht (by linarith)).1
    (Real.exp_pos (leftKappa t)).le
  rwa [leftBeta_mul_exp_kappa] at hm

theorem leftBeta_lt_small {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) : leftBeta t < 1/50000 := by
  have hb := (leftBeta_bounds ht (by linarith)).2
  have hq := leftNome_lt_ten_neg_five ht htu
  linarith

theorem left_first_large_coefficient_le_two {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftBeta t+leftRootR t/leftNome t ≤ 2 := by
  have hr := (leftRootR_bounds ht (by linarith)).2
  have hrq : leftRootR t/leftNome t < 1 := (div_lt_one (leftNome_pos t)).mpr hr
  have hb := leftBeta_lt_small ht htu
  linarith

theorem left_second_small_coefficient_lt_one {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftBeta t*leftKappa0 t+(5/4)*leftBeta t < 1 := by
  have hk0 := (leftKappa_bounds ht (by linarith)).2.2
  have hb := leftBeta_lt_small ht htu
  have hκb : leftKappa t*leftBeta t < 1/10000 := by
    rw [← exp_neg_leftKappa]
    exact kappa_mul_exp_neg_lt (leftKappa_gt ht htu)
  have hm := mul_lt_mul_of_pos_left hk0 (leftBeta_pos t)
  nlinarith

theorem leftNome_sq_mul_kappa0_lt {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    (leftNome t)^2*leftKappa0 t < 1/1000 := by
  have hq0 := leftNome_pos t
  have hq := leftNome_lt_ten_neg_five ht htu
  have hkq := leftKappa_mul_nome_lt ht htu
  have hk0 := (leftKappa_bounds ht (by linarith)).2.2
  have hm0 := mul_lt_mul_of_pos_left hk0 (sq_pos_of_pos hq0)
  have hm1 := mul_lt_mul_of_pos_right hkq hq0
  have hm2 := mul_lt_mul_of_pos_right hq hq0
  nlinarith

theorem left_second_large_coefficient_lt_one {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    (leftBeta t)^2/2+2*(leftNome t)^2*leftKappa0 t+
      (leftRootR t)^2/(2*(leftNome t)^2) < 1 := by
  have hq0 := leftNome_pos t
  have hr0 := leftRootR_pos t
  have hr := (leftRootR_bounds ht (by linarith)).2
  have hb0 := leftBeta_pos t
  have hb := leftBeta_lt_small ht htu
  have hκ0 := leftNome_sq_mul_kappa0_lt ht htu
  have hratio : (leftRootR t)^2/(2*(leftNome t)^2) ≤ 1/2 := by
    apply (div_le_iff₀ (show 0 < 2*(leftNome t)^2 by positivity)).mpr
    nlinarith
  have hb2 : (leftBeta t)^2 < 1/4 := by nlinarith
  nlinarith

theorem quad_mul_exp_neg_strictAnti :
    StrictAntiOn (fun x : ℝ => x*(x+1)*Real.exp (-x)) (Ici 3) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (by fun_prop)
  intro x hx
  have hx3 : 3 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have hd : HasDerivAt (fun y : ℝ => y*(y+1)*Real.exp (-y))
      ((-x^2+x+1)*Real.exp (-x)) x := by
    have h := ((hasDerivAt_id x).mul ((hasDerivAt_id x).add_const 1)).mul
      ((hasDerivAt_id x).neg.exp)
    simp only [Pi.neg_apply, Pi.mul_apply, id_eq] at h
    convert h using 1
    · rfl
    · ring
  rw [hd.deriv]
  exact mul_neg_of_neg_of_pos (by nlinarith [sq_nonneg (x-2)]) (Real.exp_pos _)

theorem quad_mul_exp_neg_lt {κ : ℝ} (hκ : 25/2 < κ) :
    κ*(κ+1)*Real.exp (-κ) < 1/100 := by
  have hm := quad_mul_exp_neg_strictAnti (show (25/2 : ℝ) ∈ Ici 3 by norm_num)
    (show κ ∈ Ici 3 by change 3 ≤ κ; linarith) hκ
  have hb : (25/2 : ℝ)*(25/2+1)*Real.exp (-(25/2)) < 1/100 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    nlinarith [exp_twenty_five_halves_gt]
  exact hm.trans hb

theorem left_moment_error_coefficient_lt {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    50*leftNome t*Real.exp (leftKappa t)+
      100*leftKappa t*leftNome t*leftKappa0 t+18 < 69 := by
  have hκ := leftKappa_gt ht htu
  have hκ0 : 0 < leftKappa t := by linarith
  have hq0 := leftNome_pos t
  have hk0 := (leftKappa_bounds ht (by linarith)).2.2
  have hqb := (leftBeta_bounds ht (by linarith)).1
  rw [← exp_neg_leftKappa] at hqb
  have hm0 := mul_lt_mul_of_pos_left hk0 (mul_pos hκ0 hq0)
  have hm1 := mul_le_mul_of_nonneg_left hqb (show 0 ≤ leftKappa t*(leftKappa t+1) by positivity)
  have hb := quad_mul_exp_neg_lt hκ
  have hqe := leftNome_mul_exp_kappa_le_one ht htu
  nlinarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_moment_error_coefficient_lt

/- LeftDensityBounds -/

namespace TwoAxisHelicoid
set_option maxHeartbeats 800000

theorem leftMomentDensity_nonneg {κ ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ leftMomentDensity κ ρ := by
  unfold leftMomentDensity
  positivity

theorem leftMomentDensity_exponential_le {κ ρ : ℝ} (hκ : 0 ≤ κ) :
    Real.exp (κ*((1-ρ^2)/(1+ρ^2))) ≤ Real.exp κ := by
  apply Real.exp_le_exp.mpr
  have ha : (1-ρ^2)/(1+ρ^2) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg ρ])
  nlinarith [mul_le_mul_of_nonneg_left ha hκ]

theorem leftMomentDensity_small_bound {κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    leftMomentDensity κ ρ ≤ ρ*Real.exp κ*Real.exp (-κ*ρ^2) := by
  have hr2 : ρ^2 ≤ 1 := by nlinarith
  have ha : (1-ρ^2)/(1+ρ^2) ≤ 1-ρ^2 :=
    div_le_self (by linarith) (by nlinarith [sq_nonneg ρ])
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hκ)
  rw [show κ*(1-ρ^2) = κ+(-κ*ρ^2) by ring, Real.exp_add] at he
  have hc : ρ/(1+ρ^2) ≤ ρ := div_le_self hρ0 (by nlinarith [sq_nonneg ρ])
  have hm := mul_le_mul hc he (Real.exp_pos _).le hρ0
  unfold leftMomentDensity
  nlinarith

theorem leftMomentDensity_large_bound {κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 1 ≤ ρ) :
    leftMomentDensity κ ρ ≤ 1/ρ := by
  have hρ0 : 0 < ρ := by linarith
  have ha : κ*((1-ρ^2)/(1+ρ^2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hκ (div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity))
  have he : Real.exp (κ*((1-ρ^2)/(1+ρ^2))) ≤ 1 := Real.exp_le_one_iff.mpr ha
  have hc : ρ/(1+ρ^2) ≤ 1/ρ := by
    apply (div_le_div_iff₀ (by positivity : 0 < 1+ρ^2) hρ0).mpr
    nlinarith
  unfold leftMomentDensity
  exact (mul_le_of_le_one_right (by positivity) he).trans hc

theorem left_density_weight_one_small {κ β r ρ : ℝ}
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hr : 0 ≤ r) (hrβ : r ≤ β)
    (hβe : β*Real.exp κ = 1) (hρ : 0 < ρ) :
    leftMomentDensity κ ρ*(β/ρ+r*ρ) ≤ 1 := by
  have hd : 0 < 1+ρ^2 := by positivity
  have he := leftMomentDensity_exponential_le (ρ := ρ) hκ
  have hC : (β+r*ρ^2)/(1+ρ^2) ≤ β := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right hrβ (sq_nonneg ρ)]
  have hC0 : 0 ≤ (β+r*ρ^2)/(1+ρ^2) := by positivity
  have hm := mul_le_mul hC he (Real.exp_pos _).le hβ
  rw [hβe] at hm
  have heq : leftMomentDensity κ ρ*(β/ρ+r*ρ) =
      ((β+r*ρ^2)/(1+ρ^2))*Real.exp (κ*((1-ρ^2)/(1+ρ^2))) := by
    unfold leftMomentDensity
    field_simp [hρ.ne', hd.ne']
  rw [heq]
  exact hm

theorem left_density_weight_one_large {κ β r ρ : ℝ}
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hr : 0 ≤ r) (hρ : 1 ≤ ρ) :
    leftMomentDensity κ ρ*(β/ρ+r*ρ) ≤ β/ρ^2+r := by
  have hρ0 : 0 < ρ := by linarith
  have hm := mul_le_mul_of_nonneg_right (leftMomentDensity_large_bound hκ hρ)
    (show 0 ≤ β/ρ+r*ρ by positivity)
  have he : (1/ρ)*(β/ρ+r*ρ) = β/ρ^2+r := by field_simp [hρ0.ne']
  rwa [he] at hm

theorem left_density_weight_two_small {κ β r ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 0 < ρ) :
    leftMomentDensity κ ρ*(β/ρ+r*ρ)^2 ≤
      Real.exp κ*(β^2/ρ+2*β*r*ρ+r^2*ρ^3) := by
  have he := leftMomentDensity_exponential_le (ρ := ρ) hκ
  have hc : ρ/(1+ρ^2) ≤ ρ := div_le_self hρ.le (by nlinarith [sq_nonneg ρ])
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul hc he (Real.exp_pos _).le hρ.le)
    (sq_nonneg (β/ρ+r*ρ))
  have heq : (ρ*Real.exp κ)*(β/ρ+r*ρ)^2 =
      Real.exp κ*(β^2/ρ+2*β*r*ρ+r^2*ρ^3) := by
    field_simp [hρ.ne']
    ring
  exact hm.trans_eq heq

theorem left_density_weight_two_large {κ β r ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 1 ≤ ρ) :
    leftMomentDensity κ ρ*(β/ρ+r*ρ)^2 ≤ β^2/ρ^3+2*β*r/ρ+r^2*ρ := by
  have hρ0 : 0 < ρ := by linarith
  have hm := mul_le_mul_of_nonneg_right (leftMomentDensity_large_bound hκ hρ)
    (sq_nonneg (β/ρ+r*ρ))
  have heq : (1/ρ)*(β/ρ+r*ρ)^2 = β^2/ρ^3+2*β*r/ρ+r^2*ρ := by
    field_simp [hρ0.ne']
    ring
  exact hm.trans_eq heq

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_density_weight_two_small
#print axioms TwoAxisHelicoid.left_density_weight_two_large

/- LeftMomentSubstitution -/

namespace TwoAxisHelicoid
open Set MeasureTheory
set_option maxHeartbeats 800000

noncomputable def leftMomentIntegral (t : ℝ) (j : ℕ) : ℝ :=
  ∫ ρ : ℝ in (leftNome t)..(1/leftNome t),
    leftMomentDensity (leftKappa t) ρ*(leftProductB t ρ)^j

theorem leftPathRho_endpoints (t : ℝ) :
    Real.exp (-Real.pi*(1/(2*t))) = leftNome t ∧
      Real.exp (-Real.pi*(-(1/(2*t)))) = 1/leftNome t := by
  have hp : Real.exp (-Real.pi*(1/(2*t))) = leftNome t := by
    unfold leftNome
    congr 1
    ring
  refine ⟨hp, ?_⟩
  rw [← hp]
  simp only [one_div]
  rw [← Real.exp_neg]
  congr 1
  ring

theorem leftMomentDensity_weight_continuousAt (t : ℝ) (j : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ContinuousAt (fun x => leftMomentDensity (leftKappa t) x*(leftProductB t x)^j) ρ :=
  (leftMomentDensity_continuous _).continuousAt.mul ((leftProductB_continuousAt t hρ).pow j)

theorem leftErrorMoment_eq_integral {t : ℝ} (ht : 0 < t) (j : ℕ) :
    leftErrorMoment t j = (Real.pi/t)*leftMomentIntegral t j := by
  let f : ℝ → ℝ := fun y => Real.exp (-Real.pi*y)
  let g : ℝ → ℝ := fun ρ => leftMomentDensity (leftKappa t) ρ*(leftProductB t ρ)^j
  have hf (y : ℝ) : HasDerivAt f (-Real.pi*f y) y := by
    have h := ((hasDerivAt_id y).const_mul (-Real.pi)).exp
    convert h using 1
    · rfl
    · dsimp only [f, id_eq]
      ring
  have hg : ContinuousOn g (f '' uIcc (-(1/(2*t))) (1/(2*t))) := by
    intro ρ hρ
    rcases hρ with ⟨y,hy,rfl⟩
    exact (leftMomentDensity_weight_continuousAt t j (Real.exp_ne_zero _)).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := -(1/(2*t))) (b := 1/(2*t)) (f := f) (f' := fun y => -Real.pi*f y)
    (g := g) (fun y _ => hf y) (by dsimp [f]; fun_prop) hg
  have hp := leftPathRho_endpoints t
  change (∫ y : ℝ in (-(1/(2*t)))..(1/(2*t)), g (f y)*(-Real.pi*f y)) =
    ∫ ρ : ℝ in (f (-(1/(2*t))))..(f (1/(2*t))), g ρ at hsub
  dsimp only [f] at hsub
  rw [hp.1, hp.2] at hsub
  rw [intervalIntegral.integral_symm (a := leftNome t) (b := 1/leftNome t)] at hsub
  have he : (fun y : ℝ => g (Real.exp (-Real.pi*y))*(-Real.pi*Real.exp (-Real.pi*y))) =
      (fun y : ℝ => (-t/Real.pi)*
        (‖leftComparisonFunction t (leftPathW y)‖*(leftProductB t (Real.exp (-Real.pi*y)))^j)) := by
    funext y
    rw [leftComparison_norm ht]
    dsimp only [g]
    field_simp [ht.ne', Real.pi_ne_zero]
  rw [he, intervalIntegral.integral_const_mul] at hsub
  change (-t/Real.pi)*leftErrorMoment t j = -leftMomentIntegral t j at hsub
  apply mul_left_cancel₀ (show -t/Real.pi ≠ 0 from
    div_ne_zero (neg_ne_zero.mpr ht.ne') Real.pi_ne_zero)
  calc
    _ = -leftMomentIntegral t j := hsub
    _ = (-t/Real.pi)*((Real.pi/t)*leftMomentIntegral t j) := by
      field_simp [ht.ne', Real.pi_ne_zero]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftErrorMoment_eq_integral

/- LeftMomentIntegralsBasic -/

namespace TwoAxisHelicoid
open Set MeasureTheory
set_option maxHeartbeats 800000

theorem left_positive_interval_mem {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ uIcc a b) : 0 < x := by
  exact lt_of_lt_of_le (lt_min ha hb) hx.1

theorem left_weighted_intervalIntegrable (κ β r : ℝ) (j : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun ρ : ℝ => leftMomentDensity κ ρ*(β/ρ+r*ρ)^j) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro ρ hρ
  have hρ0 := left_positive_interval_mem ha hb hρ
  apply ContinuousAt.continuousWithinAt
  exact (leftMomentDensity_continuous κ).continuousAt.mul
    (((continuousAt_const.div continuousAt_id hρ0.ne').add
      (continuousAt_const.mul continuousAt_id)).pow j)

theorem left_inv_pow_intervalIntegrable (n : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => 1/x^n) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  exact (continuousAt_const.div (continuousAt_id.pow n)
    (pow_ne_zero _ (left_positive_interval_mem ha hb hx).ne')).continuousWithinAt

theorem left_integral_inv_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in a..b, 1/x^2) = 1/a-1/b := by
  have h := integral_zpow (a := a) (b := b) (n := -2)
    (Or.inr ⟨by norm_num, notMem_uIcc_of_lt ha hb⟩)
  norm_num only [zpow_neg, zpow_natCast, one_div, Int.reduceAdd, Int.reduceNeg,
    Int.cast_neg, Int.cast_one, zpow_one, div_neg, div_one, neg_sub] at h ⊢
  exact h

theorem left_integral_inv_cube {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in a..b, 1/x^3) = 1/(2*a^2)-1/(2*b^2) := by
  have h := integral_zpow (a := a) (b := b) (n := -3)
    (Or.inr ⟨by norm_num, notMem_uIcc_of_lt ha hb⟩)
  norm_num at h
  convert h using 1 <;> field_simp [ha.ne', hb.ne']
  ring

theorem left_integral_exp_quadratic {κ q : ℝ} (hκ : 0 < κ) :
    (∫ x : ℝ in q..1, x*Real.exp (-κ*x^2)) =
      (Real.exp (-κ*q^2)-Real.exp (-κ))/(2*κ) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -Real.exp (-κ*y^2)/(2*κ))
      (x*Real.exp (-κ*x^2)) x := by
    have h := (((((hasDerivAt_id x).pow 2).const_mul (-κ)).exp).neg).div_const (2*κ)
    simp only [Pi.pow_apply, Pi.neg_apply, id_eq, Nat.reduceSub, pow_one, mul_one] at h
    convert h using 1
    field_simp [hκ.ne']
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := q) (b := 1)
    (fun x _ => hd x) (by apply Continuous.intervalIntegrable; fun_prop)
  convert h using 1
  simp only [one_pow, mul_one]
  ring

theorem left_integral_exp_quadratic_le {κ q : ℝ} (hκ : 0 < κ) :
    (∫ x : ℝ in q..1, x*Real.exp (-κ*x^2)) ≤ 1/(2*κ) := by
  rw [left_integral_exp_quadratic hκ]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have he : Real.exp (-κ*q^2) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg q))
  linarith [Real.exp_pos (-κ)]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_integral_exp_quadratic_le

/- LeftMomentZeroOne -/

namespace TwoAxisHelicoid
open Set MeasureTheory
set_option maxHeartbeats 800000

theorem left_density_integral_small {κ q : ℝ} (hκ : 0 < κ)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (∫ ρ : ℝ in q..1, leftMomentDensity κ ρ) ≤ Real.exp κ/(2*κ) := by
  have hc : Continuous (fun x : ℝ => Real.exp κ*(x*Real.exp (-κ*x^2))) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) hq1
    ((leftMomentDensity_continuous κ).intervalIntegrable q 1) (hc.intervalIntegrable q 1)
    (fun ρ hρ => by
      have h := leftMomentDensity_small_bound hκ.le (hq.le.trans hρ.1) hρ.2
      convert h using 1
      ring)
  rw [intervalIntegral.integral_const_mul] at hm
  exact hm.trans (by
    have h := mul_le_mul_of_nonneg_left (left_integral_exp_quadratic_le (q := q) hκ)
      (Real.exp_pos κ).le
    simpa only [mul_one_div] using h)

theorem left_density_integral_large {κ q : ℝ} (hκ : 0 ≤ κ)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (∫ ρ : ℝ in 1..(1/q), leftMomentDensity κ ρ) ≤ Real.log (1/q) := by
  have hR : 1 ≤ 1/q := (le_div_iff₀ hq).mpr (by simpa using hq1)
  have hi := left_inv_pow_intervalIntegrable 1 (a := 1) (b := 1/q)
    (by norm_num) (one_div_pos.mpr hq)
  simp only [pow_one] at hi
  have hm := intervalIntegral.integral_mono_on (μ := volume) hR
    ((leftMomentDensity_continuous κ).intervalIntegrable _ _) hi
    (fun ρ hρ => leftMomentDensity_large_bound hκ hρ.1)
  rw [integral_one_div_of_pos (by norm_num) (one_div_pos.mpr hq), div_one] at hm
  exact hm

theorem left_weight_one_integral_small {κ β r q : ℝ}
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hr : 0 ≤ r) (hrβ : r ≤ β)
    (hβe : β*Real.exp κ = 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    (∫ ρ : ℝ in q..1, leftMomentDensity κ ρ*(β/ρ+r*ρ)) ≤ 1 := by
  have hi := left_weighted_intervalIntegrable κ β r 1 hq (by norm_num : (0 : ℝ) < 1)
  simp only [pow_one] at hi
  have hm := intervalIntegral.integral_mono_on (μ := volume) hq1 hi intervalIntegrable_const
    (fun ρ hρ => left_density_weight_one_small hκ hβ hr hrβ hβe (hq.trans_le hρ.1))
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hm
  linarith

theorem left_weight_one_integral_large {κ β r q : ℝ}
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hr : 0 ≤ r) (hq : 0 < q) (hq1 : q ≤ 1) :
    (∫ ρ : ℝ in 1..(1/q), leftMomentDensity κ ρ*(β/ρ+r*ρ)) ≤ β+r/q := by
  have hR0 : 0 < 1/q := one_div_pos.mpr hq
  have hR : 1 ≤ 1/q := (le_div_iff₀ hq).mpr (by simpa using hq1)
  have hi := left_weighted_intervalIntegrable κ β r 1 (by norm_num : (0 : ℝ) < 1) hR0
  simp only [pow_one] at hi
  have hb := (left_inv_pow_intervalIntegrable 2 (a := 1) (by norm_num) hR0).const_mul β
  have hm := intervalIntegral.integral_mono_on (μ := volume) hR hi (hb.add intervalIntegrable_const)
    (fun ρ hρ => by
      have h := left_density_weight_one_large (β := β) (r := r) hκ hβ hr hρ.1
      simpa only [mul_one_div] using h)
  rw [intervalIntegral.integral_add hb intervalIntegrable_const,
    intervalIntegral.integral_const_mul, left_integral_inv_sq (by norm_num) hR0,
    intervalIntegral.integral_const] at hm
  simp only [one_div_one, one_div_one_div, smul_eq_mul] at hm
  have hbound : β*(1-q)+(1/q-1)*r ≤ β+r/q := by
    have hp := mul_nonneg hβ hq.le
    have he : r/q = (1/q)*r := by ring
    rw [he]
    nlinarith
  exact hm.trans hbound

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_density_integral_small
#print axioms TwoAxisHelicoid.left_weight_one_integral_large

/- LeftMomentTwo -/

namespace TwoAxisHelicoid
open Set MeasureTheory
set_option maxHeartbeats 1000000

theorem left_weight_two_small_majorant_integral {β r q : ℝ} (hq : 0 < q) :
    (∫ ρ : ℝ in q..1, β^2/ρ+2*β*r*ρ+r^2*ρ^3) =
      β^2*Real.log (1/q)+β*r*(1-q^2)+(r^2/4)*(1-q^4) := by
  have hi := left_inv_pow_intervalIntegrable 1 hq (by norm_num : (0 : ℝ) < 1)
  simp only [pow_one] at hi
  have h0 := hi.const_mul (β^2)
  have h1 : IntervalIntegrable (fun x : ℝ => 2*β*r*x) volume q 1 :=
    (by fun_prop : Continuous (fun x : ℝ => 2*β*r*x)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => r^2*x^3) volume q 1 :=
    (by fun_prop : Continuous (fun x : ℝ => r^2*x^3)).intervalIntegrable _ _
  simp_rw [div_eq_mul_one_div (β^2)]
  rw [intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1, intervalIntegral.integral_const_mul,
    integral_one_div_of_pos hq (by norm_num), intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const_mul, integral_pow]
  norm_num only [one_pow, Nat.cast_ofNat]
  ring

theorem left_weight_two_integral_small {κ β r q : ℝ}
    (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (hr : 0 ≤ r) (hrβ : r ≤ β)
    (hβe : β*Real.exp κ = 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    (∫ ρ : ℝ in q..1, leftMomentDensity κ ρ*(β/ρ+r*ρ)^2) ≤
      β*Real.log (1/q)+(5/4)*β := by
  have hi := left_weighted_intervalIntegrable κ β r 2 hq (by norm_num : (0 : ℝ) < 1)
  have hj : IntervalIntegrable (fun ρ : ℝ => Real.exp κ*(β^2/ρ+2*β*r*ρ+r^2*ρ^3))
      volume q 1 := by
    apply ContinuousOn.intervalIntegrable
    intro ρ hρ
    have hρ0 := left_positive_interval_mem hq (by norm_num : (0 : ℝ) < 1) hρ
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := exact hρ0.ne')
  have hm := intervalIntegral.integral_mono_on (μ := volume) hq1 hi hj
    (fun ρ hρ => left_density_weight_two_small (β := β) (r := r) hκ (hq.trans_le hρ.1))
  rw [intervalIntegral.integral_const_mul, left_weight_two_small_majorant_integral hq] at hm
  have hpoly : β^2*Real.log (1/q)+β*r*(1-q^2)+(r^2/4)*(1-q^4) ≤
      β^2*Real.log (1/q)+β*r+r^2/4 := by
    have hp1 := mul_nonneg (mul_nonneg hβ hr) (sq_nonneg q)
    have hp2 := mul_nonneg (sq_nonneg r) (pow_nonneg hq.le 4)
    nlinarith
  have hm2 := mul_le_mul_of_nonneg_left hpoly (Real.exp_pos κ).le
  have heq : Real.exp κ*(β^2*Real.log (1/q)+β*r+r^2/4) =
      (β*Real.exp κ)*(β*Real.log (1/q)+r)+(r^2*Real.exp κ)/4 := by ring
  rw [heq, hβe, one_mul] at hm2
  have hr2 : r^2*Real.exp κ ≤ β := by
    have hsq : r^2 ≤ β^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (Real.exp_pos κ).le
    have he : β^2*Real.exp κ = β := by
      calc
        _ = β*(β*Real.exp κ) := by ring
        _ = β := by rw [hβe, mul_one]
    rwa [he] at h
  exact hm.trans (hm2.trans (by nlinarith))

theorem left_weight_two_large_majorant_integral {β r q : ℝ} (hq : 0 < q) :
    (∫ ρ : ℝ in 1..(1/q), β^2/ρ^3+2*β*r/ρ+r^2*ρ) =
      (β^2/2)*(1-q^2)+2*β*r*Real.log (1/q)+(r^2/2)*((1/q)^2-1) := by
  have hR0 := one_div_pos.mpr hq
  have h0 := (left_inv_pow_intervalIntegrable 3 (a := 1) (by norm_num) hR0).const_mul (β^2)
  have hi := left_inv_pow_intervalIntegrable 1 (a := 1) (by norm_num) hR0
  simp only [pow_one] at hi
  have h1 := hi.const_mul (2*β*r)
  have h2 : IntervalIntegrable (fun x : ℝ => r^2*x) volume 1 (1/q) :=
    (by fun_prop : Continuous (fun x : ℝ => r^2*x)).intervalIntegrable _ _
  simp_rw [div_eq_mul_one_div (β^2), div_eq_mul_one_div (2*β*r)]
  rw [intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1, intervalIntegral.integral_const_mul,
    left_integral_inv_cube (by norm_num) hR0, intervalIntegral.integral_const_mul,
    integral_one_div_of_pos (by norm_num) hR0, intervalIntegral.integral_const_mul,
    integral_id]
  norm_num only [one_pow, div_one]
  field_simp [hq.ne']

theorem left_weight_two_integral_large {κ β r q : ℝ}
    (hκ : 0 ≤ κ) (hq : 0 < q) (hq1 : q ≤ 1) :
    (∫ ρ : ℝ in 1..(1/q), leftMomentDensity κ ρ*(β/ρ+r*ρ)^2) ≤
      β^2/2+2*β*r*Real.log (1/q)+r^2/(2*q^2) := by
  have hR0 := one_div_pos.mpr hq
  have hR : 1 ≤ 1/q := (le_div_iff₀ hq).mpr (by simpa using hq1)
  have hi := left_weighted_intervalIntegrable κ β r 2 (by norm_num : (0 : ℝ) < 1) hR0
  have hj : IntervalIntegrable (fun ρ : ℝ => β^2/ρ^3+2*β*r/ρ+r^2*ρ)
      volume 1 (1/q) := by
    apply ContinuousOn.intervalIntegrable
    intro ρ hρ
    have hρ0 := left_positive_interval_mem (by norm_num : (0 : ℝ) < 1) hR0 hρ
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hm := intervalIntegral.integral_mono_on (μ := volume) hR hi hj
    (fun ρ hρ => left_density_weight_two_large (β := β) (r := r) hκ hρ.1)
  rw [left_weight_two_large_majorant_integral hq] at hm
  have he : r^2/(2*q^2) = (r^2/2)*(1/q)^2 := by ring
  rw [he]
  have hp := mul_nonneg (sq_nonneg β) (sq_nonneg q)
  exact hm.trans (by nlinarith [sq_nonneg r])

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.left_weight_two_integral_small
#print axioms TwoAxisHelicoid.left_weight_two_integral_large

/- LeftMomentBounds -/

namespace TwoAxisHelicoid
open Set MeasureTheory
set_option maxHeartbeats 1000000

theorem leftNome_log_inv (t : ℝ) : Real.log (1/leftNome t) = leftKappa0 t := by
  unfold leftNome leftKappa0
  rw [one_div, Real.log_inv, Real.log_exp]
  ring

theorem leftBeta_mul_rootR (t : ℝ) : leftBeta t*leftRootR t = (leftNome t)^2 := by
  unfold leftBeta
  exact div_mul_cancel₀ _ (leftRootR_pos t).ne'

theorem leftMomentIntegral_split (t : ℝ) (j : ℕ) :
    leftMomentIntegral t j =
      (∫ ρ : ℝ in (leftNome t)..1, leftMomentDensity (leftKappa t) ρ*(leftProductB t ρ)^j)+
      (∫ ρ : ℝ in 1..(1/leftNome t), leftMomentDensity (leftKappa t) ρ*(leftProductB t ρ)^j) := by
  have h1 := left_weighted_intervalIntegrable (leftKappa t) (leftBeta t) (leftRootR t) j
    (leftNome_pos t) (by norm_num : (0 : ℝ) < 1)
  have h2 := left_weighted_intervalIntegrable (leftKappa t) (leftBeta t) (leftRootR t) j
    (by norm_num : (0 : ℝ) < 1) (one_div_pos.mpr (leftNome_pos t))
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

theorem leftMomentIntegral_zero_le {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftMomentIntegral t 0 ≤ Real.exp (leftKappa t)/(2*leftKappa t)+leftKappa0 t := by
  have hκ : 0 < leftKappa t := by linarith [leftKappa_gt ht htu]
  have hq1 : leftNome t ≤ 1 := (leftNome_lt_ten_neg_five ht htu).le.trans (by norm_num)
  have hsmall := left_density_integral_small hκ (leftNome_pos t) hq1
  have hlarge := left_density_integral_large hκ.le (leftNome_pos t) hq1
  rw [leftNome_log_inv] at hlarge
  rw [leftMomentIntegral_split]
  simp only [pow_zero, mul_one]
  exact add_le_add hsmall hlarge

theorem leftMomentIntegral_one_le {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftMomentIntegral t 1 ≤ 3 := by
  have hκ : 0 ≤ leftKappa t := by linarith [leftKappa_gt ht htu]
  have hq1 : leftNome t ≤ 1 := (leftNome_lt_ten_neg_five ht htu).le.trans (by norm_num)
  have hsmall := left_weight_one_integral_small hκ (leftBeta_pos t).le (leftRootR_pos t).le
    (leftRootR_le_beta ht htu) (leftBeta_mul_exp_kappa t) (leftNome_pos t) hq1
  have hlarge := left_weight_one_integral_large hκ (leftBeta_pos t).le (leftRootR_pos t).le
    (leftNome_pos t) hq1
  have hb := left_first_large_coefficient_le_two ht htu
  rw [leftMomentIntegral_split]
  simp only [pow_one, leftProductB]
  linarith

theorem leftMomentIntegral_two_le {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftMomentIntegral t 2 ≤ 2 := by
  have hκ : 0 ≤ leftKappa t := by linarith [leftKappa_gt ht htu]
  have hq1 : leftNome t ≤ 1 := (leftNome_lt_ten_neg_five ht htu).le.trans (by norm_num)
  have hsmall := left_weight_two_integral_small hκ (leftBeta_pos t).le (leftRootR_pos t).le
    (leftRootR_le_beta ht htu) (leftBeta_mul_exp_kappa t) (leftNome_pos t) hq1
  have hlarge := left_weight_two_integral_large (β := leftBeta t) (r := leftRootR t)
    hκ (leftNome_pos t) hq1
  rw [leftNome_log_inv] at hsmall hlarge
  have he : 2*leftBeta t*leftRootR t = 2*(leftNome t)^2 := by
    rw [mul_assoc, leftBeta_mul_rootR]
  rw [he] at hlarge
  have hb1 := left_second_small_coefficient_lt_one ht htu
  have hb2 := left_second_large_coefficient_lt_one ht htu
  rw [leftMomentIntegral_split]
  simp only [leftProductB]
  linarith

theorem leftErrorMoment_zero_le {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftErrorMoment t 0 ≤ (Real.pi/t)*
      (Real.exp (leftKappa t)/(2*leftKappa t)+leftKappa0 t) := by
  rw [leftErrorMoment_eq_integral ht]
  exact mul_le_mul_of_nonneg_left (leftMomentIntegral_zero_le ht htu) (by positivity)

theorem leftErrorMoment_one_le {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftErrorMoment t 1 ≤ (Real.pi/t)*3 := by
  rw [leftErrorMoment_eq_integral ht]
  exact mul_le_mul_of_nonneg_left (leftMomentIntegral_one_le ht htu) (by positivity)

theorem leftErrorMoment_two_le {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftErrorMoment t 2 ≤ (Real.pi/t)*2 := by
  rw [leftErrorMoment_eq_integral ht]
  exact mul_le_mul_of_nonneg_left (leftMomentIntegral_two_le ht htu) (by positivity)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftErrorMoment_zero_le
#print axioms TwoAxisHelicoid.leftErrorMoment_one_le
#print axioms TwoAxisHelicoid.leftErrorMoment_two_le
