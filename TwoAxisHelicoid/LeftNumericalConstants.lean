import TwoAxisHelicoid.LeftRootParameters
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace TwoAxisHelicoid
open Set
set_option maxHeartbeats 800000

theorem exp_two_gt_seven : (7 : ℝ) < Real.exp 2 := by
  have h : (27/10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 := pow_lt_pow_left₀ h (by norm_num : (0 : ℝ) ≤ 27/10) (by decide : 2 ≠ 0)
  have he : (Real.exp 1)^2 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he] at h2
  norm_num at h2
  linarith

theorem exp_twelve_gt : (7 : ℝ)^6 < Real.exp 12 := by
  have h := pow_lt_pow_left₀ exp_two_gt_seven (by norm_num : (0 : ℝ) ≤ 7)
    (by decide : 6 ≠ 0)
  have he : (Real.exp 2)^6 = Real.exp 12 := by rw [← Real.exp_nat_mul]; norm_num
  rwa [he] at h

theorem exp_twenty_five_halves_gt : (3/2 : ℝ)*7^6 < Real.exp (25/2) := by
  have hhalf : (3/2 : ℝ) < Real.exp (1/2) := by
    have h := Real.add_one_lt_exp (by norm_num : (1/2 : ℝ) ≠ 0)
    linarith
  have h := mul_lt_mul hhalf exp_twelve_gt.le (by norm_num : (0 : ℝ) < 7^6)
    (Real.exp_pos _).le
  rw [← Real.exp_add] at h
  norm_num at h ⊢
  exact h

theorem leftKappa0_gt {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    (314/25 : ℝ) < leftKappa0 t := by
  unfold leftKappa0
  apply (lt_div_iff₀ (by positivity : 0 < 2*t)).mpr
  nlinarith [Real.pi_gt_d2]

theorem leftNome_lt_ten_neg_five {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftNome t < 1/100000 := by
  have hk := leftKappa0_gt ht htu
  have he : leftNome t = Real.exp (-leftKappa0 t) := by
    unfold leftNome leftKappa0
    congr 1
    ring
  have hlarge : (100000 : ℝ) < Real.exp 12 := by
    exact (by norm_num : (100000 : ℝ) < 7^6).trans exp_twelve_gt
  have hb : Real.exp (-12) < 1/100000 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num) hlarge
  rw [he]
  exact (Real.exp_lt_exp.mpr (by linarith)).trans hb

theorem leftKappa_gt {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    (25/2 : ℝ) < leftKappa t := by
  have h0 := leftKappa0_gt ht htu
  have hq := leftNome_lt_ten_neg_five ht htu
  have hk := (leftKappa_bounds ht (by linarith)).1
  linarith

theorem exp_neg_leftKappa (t : ℝ) : Real.exp (-leftKappa t) = leftBeta t := by
  unfold leftKappa
  rw [neg_neg, Real.exp_log (leftBeta_pos t)]

theorem mul_exp_neg_strictAnti : StrictAntiOn (fun x : ℝ => x*Real.exp (-x)) (Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (by fun_prop)
  intro x hx
  have hx1 : 1 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have hd : HasDerivAt (fun y : ℝ => y*Real.exp (-y)) ((1-x)*Real.exp (-x)) x := by
    have h := (hasDerivAt_id x).mul ((hasDerivAt_id x).neg.exp)
    simp only [Pi.neg_apply, id_eq] at h
    convert h using 1
    · rfl
    · ring
  rw [hd.deriv]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)

theorem kappa_mul_exp_neg_lt {k : ℝ} (hk : 25/2 < k) :
    k*Real.exp (-k) < 1/10000 := by
  have hm := mul_exp_neg_strictAnti (show (25/2 : ℝ) ∈ Ici 1 by norm_num)
    (show k ∈ Ici 1 by change 1 ≤ k; linarith) hk
  have hb : (25/2 : ℝ)*Real.exp (-(25/2)) < 1/10000 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    nlinarith [exp_twenty_five_halves_gt]
  exact hm.trans hb

theorem leftKappa_mul_nome_lt {t : ℝ} (ht : 0 < t) (htu : t ≤ 1/8) :
    leftKappa t*leftNome t < 1/10000 := by
  have hk := leftKappa_gt ht htu
  have hq := (leftBeta_bounds ht (by linarith)).1
  rw [← exp_neg_leftKappa] at hq
  exact (mul_le_mul_of_nonneg_left hq (by linarith)).trans_lt (kappa_mul_exp_neg_lt hk)

theorem exp_div_sq_strictMono : StrictMonoOn (fun x : ℝ => Real.exp x/x^2) (Ici 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (by change 2 ≤ x at hx; linarith))
  intro x hx
  have hx2 : 2 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have hx0 : 0 < x := by linarith
  have hd : HasDerivAt (fun y : ℝ => Real.exp y/y^2)
      (Real.exp x*(x-2)/x^3) x := by
    have h := (Real.hasDerivAt_exp x).div ((hasDerivAt_id x).pow 2)
      (pow_ne_zero _ hx0.ne')
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one] at h
    convert h using 1
    · rfl
    · field_simp [hx0.ne']
  rw [hd.deriv]
  exact div_pos (mul_pos (Real.exp_pos _) (by linarith)) (pow_pos hx0 _)

theorem comparison_exponential_lower_bound {k : ℝ} (hk : 25/2 < k) :
    (70 : ℝ) < Real.exp k/(16*k^2) := by
  have hm := exp_div_sq_strictMono (show (25/2 : ℝ) ∈ Ici 2 by norm_num)
    (show k ∈ Ici 2 by change 2 ≤ k; linarith) hk
  have hb : (1120 : ℝ) < Real.exp (25/2)/(25/2)^2 := by
    apply (lt_div_iff₀ (by norm_num)).mpr
    nlinarith [exp_twenty_five_halves_gt]
  have h : (1120 : ℝ) < Real.exp k/k^2 := hb.trans hm
  have he : Real.exp k/(16*k^2) = (Real.exp k/k^2)/16 := by ring
  rw [he]
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.leftKappa_mul_nome_lt
#print axioms TwoAxisHelicoid.comparison_exponential_lower_bound
