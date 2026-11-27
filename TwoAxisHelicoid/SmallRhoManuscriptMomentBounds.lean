import TwoAxisHelicoid.LeftPathMomentSubinterval
import TwoAxisHelicoid.SmallRhoPointwiseEstimates
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace TwoAxisHelicoid
open Filter Set MeasureTheory

/-- The part of the manuscript moment with ρ ≤ 1 is the positive y half. -/
noncomputable def smallRhoPathMoment (t : ℝ) (j : ℕ) : ℝ :=
  ∫ y : ℝ in 0..(1/(2*t)), ‖leftComparisonFunction t (leftPathW y)‖*
    (leftProductB t (Real.exp (-Real.pi*y)))^j

theorem smallRhoPathMoment_eq_density {t : ℝ} (ht : 0 < t) (j : ℕ) :
    smallRhoPathMoment t j = (Real.pi/t)*
      ∫ x : ℝ in (leftNome t)..1, leftMomentDensity (leftKappa t) x*(leftProductB t x)^j := by
  simpa only [smallRhoPathMoment, (leftPathRho_endpoints t).1, mul_zero, Real.exp_zero] using
    left_path_moment_subinterval ht j 0 (1/(2*t))

private theorem gaussian_mass_small_interval {κ q : ℝ} (hk : 0 < κ) (hq : 0 < q) (hu : q ≤ 1) :
    (∫ x : ℝ in q..1, Real.exp (-κ*x^2)) ≤ Real.sqrt Real.pi/(2*Real.sqrt κ) := by
  rw [intervalIntegral.integral_of_le hu]
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, Real.exp (-κ*x^2) :=
      setIntegral_mono_set (integrable_exp_neg_mul_sq hk).integrableOn
        (ae_of_all _ fun _ => (Real.exp_pos _).le) (ae_of_all _ fun _ h => hq.trans h.1)
    _ = _ := by rw [integral_gaussian_Ioi,Real.sqrt_div Real.pi_pos.le]; ring

/-- Both inequalities of the display on line 1302, for the actual half path. -/
theorem smallRho_first_moment_printed {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    let κ := leftKappa t
    let b := leftBeta t
    let r := leftRootR t
    let M := Real.pi*Real.exp κ/t*
      (b*Real.sqrt Real.pi/(2*Real.sqrt κ)+r*Real.sqrt Real.pi/(4*κ^(3/2:ℝ)))
    smallRhoPathMoment t 1 ≤ M ∧ M ≤ (Real.pi/t)*(2/Real.sqrt κ) := by
  intro κ b r M
  let q := leftNome t
  have hk : 0 < κ := by have h := leftKappa_gt ht htu; dsimp [κ]; linarith
  have k1 : 1 ≤ κ := by have h := leftKappa_gt ht htu; dsimp [κ]; linarith
  have qb : 0 < q := leftNome_pos t
  have qu : q ≤ 1 := (leftNome_lt_ten_neg_five ht htu).le.trans (by norm_num)
  have bp : 0 < b := leftBeta_pos t
  have rp : 0 < r := leftRootR_pos t
  have rb : r ≤ b := leftRootR_le_beta ht htu
  have be : b*Real.exp κ = 1 := leftBeta_mul_exp_kappa t
  have tg : 0 ≤ Real.pi/t := (div_pos Real.pi_pos ht).le
  have scale : M = (Real.pi/t)*(Real.exp κ*
      (b*Real.sqrt Real.pi/(2*Real.sqrt κ)+r*Real.sqrt Real.pi/(4*κ^(3/2:ℝ)))) := by dsimp [M]; ring
  rw [scale]
  constructor
  · rw [smallRhoPathMoment_eq_density ht]
    apply mul_le_mul_of_nonneg_left _ tg
    have hi := left_weighted_intervalIntegrable κ b r 1 qb (by norm_num : (0:ℝ)<1)
    have hj : Continuous (fun x : ℝ => (b*Real.exp κ)*Real.exp (-κ*x^2)) := by fun_prop
    have le := intervalIntegral.integral_mono_on (μ := volume) qu hi (hj.intervalIntegrable _ _)
      (fun x h => by simpa only [pow_one, leftMomentDensity] using small_rho_first_weight_upper hk.le bp.le rb (qb.trans_le h.1) h.2)
    rw [intervalIntegral.integral_const_mul] at le
    have bound := le.trans (mul_le_mul_of_nonneg_left (gaussian_mass_small_interval hk qb qu) (by positivity))
    change (∫ x : ℝ in q..1, leftMomentDensity κ x*(b/x+r*x)^1) ≤ _
    have pos : 0 ≤ Real.exp κ*(r*Real.sqrt Real.pi/(4*κ^(3/2:ℝ))) := by positivity
    calc
      _ ≤ b*Real.exp κ*(Real.sqrt Real.pi/(2*Real.sqrt κ)) := bound
      _ = Real.exp κ*(b*Real.sqrt Real.pi/(2*Real.sqrt κ)) := by ring
      _ ≤ _ := by
        rw [mul_add]
        exact le_add_of_nonneg_right pos
  · apply mul_le_mul_of_nonneg_left _ tg
    have s : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hk
    have pow32 : κ^(3/2:ℝ) = κ*Real.sqrt κ := by
      rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hk,Real.rpow_one,← Real.sqrt_eq_rpow]
    rw [pow32]
    have repr : Real.exp κ*(b*Real.sqrt Real.pi/(2*Real.sqrt κ)+r*Real.sqrt Real.pi/(4*(κ*Real.sqrt κ))) =
        ((b*Real.exp κ)*Real.sqrt Real.pi/2+(r*Real.exp κ)*Real.sqrt Real.pi/(4*κ))/Real.sqrt κ := by
      field_simp [s.ne',hk.ne']
    rw [repr,be,one_mul]
    apply div_le_div_of_nonneg_right _ s.le
    have sqrtpi : Real.sqrt Real.pi ≤ 2 := by
      nlinarith [Real.sq_sqrt Real.pi_pos.le,Real.pi_lt_four,sq_nonneg (Real.sqrt Real.pi-2)]
    have re := (mul_le_mul_of_nonneg_right rb (Real.exp_pos κ).le).trans_eq be
    have p : (r*Real.exp κ)*Real.sqrt Real.pi ≤ 2 :=
      (mul_le_mul re sqrtpi (Real.sqrt_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have p' : (r*Real.exp κ)*Real.sqrt Real.pi/(4*κ) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    linarith

/-- All inequalities of the display on line 1314. -/
theorem smallRho_second_moment_printed {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    let κ := leftKappa t
    let b := leftBeta t
    let r := leftRootR t
    let q := leftNome t
    let M := Real.pi*Real.exp κ/t*(b^2*leftKappa0 t+q^2/κ+r^2/(2*κ^2))
    smallRhoPathMoment t 2 ≤ M ∧ M ≤ (Real.pi/t)*(b*(κ+2)) ∧ (Real.pi/t)*(b*(κ+2)) < Real.pi/t := by
  intro κ b r q M
  have kg : 25/2 < κ := leftKappa_gt ht htu
  have k1 : 1 ≤ κ := by linarith
  have k2 : 2 ≤ κ := by linarith
  have kp : 0 < κ := by linarith
  have bp : 0 < b := leftBeta_pos t
  have rp : 0 < r := leftRootR_pos t
  have qp : 0 < q := leftNome_pos t
  have qu : q ≤ 1 := (leftNome_lt_ten_neg_five ht htu).le.trans (by norm_num)
  have rb : r ≤ b := leftRootR_le_beta ht htu
  have be : b*Real.exp κ = 1 := leftBeta_mul_exp_kappa t
  have tg : 0 < Real.pi/t := div_pos Real.pi_pos ht
  have scale : M = (Real.pi/t)*(Real.exp κ*(b^2*leftKappa0 t+q^2/κ+r^2/(2*κ^2))) := by dsimp [M]; ring
  rw [scale]
  refine ⟨?_,?_,?_⟩
  · rw [smallRhoPathMoment_eq_density ht]
    apply mul_le_mul_of_nonneg_left _ tg.le
    have hi := left_weighted_intervalIntegrable κ b r 2 qp (by norm_num : (0:ℝ)<1)
    have hj := (left_inv_pow_intervalIntegrable 1 qp (by norm_num : (0:ℝ)<1))
    simp only [pow_one] at hj
    have le := intervalIntegral.integral_mono_on (μ := volume) qu hi (hj.const_mul (Real.exp κ*b^2))
      (fun x h => small_rho_second_weight_upper k1 bp.le rp.le rb (qp.trans_le h.1) h.2)
    rw [intervalIntegral.integral_const_mul,integral_one_div_of_pos qp (by norm_num)] at le
    change (∫ x : ℝ in q..1, leftMomentDensity κ x*(b/x+r*x)^2) ≤ _
    have logq : Real.log (1/q) = leftKappa0 t := leftNome_log_inv t
    rw [logq] at le
    calc
      _ ≤ (Real.exp κ*b^2)*leftKappa0 t := le
      _ = Real.exp κ*(b^2*leftKappa0 t) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by linarith only [div_nonneg (sq_nonneg q) kp.le,
          div_nonneg (sq_nonneg r) (show 0 ≤ 2*κ^2 by positivity)]) (Real.exp_pos _).le
  · apply mul_le_mul_of_nonneg_left _ tg.le
    have qs : q^2 ≤ b^2 := pow_le_pow_left₀ qp.le (leftBeta_bounds ht (by linarith)).1 2
    have rs : r^2 ≤ b^2 := pow_le_pow_left₀ rp.le rb 2
    have hqterm : q^2/κ ≤ b^2/2 := by
      apply (div_le_iff₀ kp).mpr
      nlinarith only [qs,mul_le_mul_of_nonneg_right k2 (sq_nonneg b)]
    have sqone : 1 ≤ κ^2 := by nlinarith [sq_nonneg (κ-1)]
    have hrterm : r^2/(2*κ^2) ≤ b^2/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [rs,mul_le_mul_of_nonneg_right sqone (sq_nonneg b)]
    have k0 : leftKappa0 t < κ+1 := (leftKappa_bounds ht (by linarith)).2.2
    calc
      _ ≤ Real.exp κ*(b^2*(leftKappa0 t+1)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hqterm,hrterm]) (Real.exp_pos _).le
      _ = (b*Real.exp κ)*(b*(leftKappa0 t+1)) := by ring
      _ ≤ _ := by rw [be,one_mul]; exact mul_le_mul_of_nonneg_left (by linarith) bp.le
  · have kb : κ*b < 1/10000 := by
      change leftKappa t*leftBeta t < 1/10000
      rw [← exp_neg_leftKappa]
      exact kappa_mul_exp_neg_lt kg
    have bs : b < 1/50000 := leftBeta_lt_small ht htu
    exact (mul_lt_mul_of_pos_left (show b*(κ+2)<1 by nlinarith) tg).trans_eq (mul_one _)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.smallRhoPathMoment_eq_density
#print axioms TwoAxisHelicoid.smallRho_first_moment_printed
#print axioms TwoAxisHelicoid.smallRho_second_moment_printed
