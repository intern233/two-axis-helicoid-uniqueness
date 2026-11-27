import TwoAxisHelicoid.OddSineFactor
import TwoAxisHelicoid.ThetaConvergence
import TwoAxisHelicoid.ExpEnclosure

namespace TwoAxisHelicoid
open Complex

noncomputable def thetaReducedTerm (t : ℝ) (n : ℕ) (v : ℂ) : ℂ :=
  thetaSign n*(Real.exp (-Real.pi*t*n*(n+1)/2):ℂ)*oddSineFactor n v

noncomputable def thetaReduced (t : ℝ) (v : ℂ) : ℂ := ∑' n, thetaReducedTerm t n v

theorem thetaReducedTerm_norm_le (t : ℝ) (n : ℕ) (v : ℂ) :
    ‖thetaReducedTerm t n v‖ ≤ Real.exp (-|v.im|)*thetaMajorant t |v.im| 1 n := by
  calc
    ‖thetaReducedTerm t n v‖ = Real.exp (-Real.pi*t*n*(n+1)/2)*‖oddSineFactor n v‖ := by
      simp only [thetaReducedTerm, norm_mul, thetaSign_norm, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-Real.pi*t*n*(n+1)/2)*((2*n+1)*Real.exp (2*n*|v.im|)) :=
      mul_le_mul_of_nonneg_left (oddSineFactor_norm_le n v) (Real.exp_nonneg _)
    _ = _ := by
      simp only [thetaMajorant,pow_one]
      rw [show -Real.pi*t*n*(n+1)/2+(2*n+1)*|v.im| =
        -Real.pi*t*n*(n+1)/2+2*n*|v.im|+|v.im| by ring]
      simp only [Real.exp_add, Real.exp_neg]
      field_simp

theorem thetaReducedTerm_summable {t : ℝ} (ht : 0 < t) (v : ℂ) :
    Summable (fun n => thetaReducedTerm t n v) :=
  ((thetaMajorant_summable ht |v.im| 1).mul_left (Real.exp (-|v.im|))).of_norm_bounded
    (fun n => thetaReducedTerm_norm_le t n v)

theorem thetaJet_eq_sin_mul_reduced (t : ℝ) (v : ℂ) :
    thetaJet t 0 v = Complex.sin v*thetaReduced t v := by
  unfold thetaJet thetaReduced
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [thetaTerm,pow_zero,mul_one,sineJet_zero,sin_odd_multiple,thetaReducedTerm]
  ring

theorem thetaReducedTerm_zero (t : ℝ) (v : ℂ) : thetaReducedTerm t 0 v = 1 := by
  simp [thetaReducedTerm,thetaSign,oddSineFactor]

theorem exp_neg_half_pi_le {t : ℝ} (ht : 43/50 ≤ t) :
    Real.exp (-Real.pi*t/2) ≤ 7/25 := by
  have hp : (129/100:ℝ) ≤ Real.pi*t/2 := by
    have ht0 : 0 ≤ t := by linarith
    nlinarith [Real.pi_gt_three]
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 129/100) 5
  norm_num [Finset.sum_range_succ] at hs
  have he : (25/7:ℝ) ≤ Real.exp (Real.pi*t/2) :=
    le_trans (by linarith) (Real.exp_le_exp.mpr hp)
  rw [show -Real.pi*t/2 = -(Real.pi*t/2) by ring, Real.exp_neg]
  rw [← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  nlinarith

theorem odd_factor_nat_bound (n : ℕ) : (2*(n:ℝ)+3) ≤ 3*2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ,pow_succ]
    have hp : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    nlinarith

theorem thetaReducedTerm_strip_bound {t : ℝ} (ht : 43/50 ≤ t) {v : ℂ}
    (hv : |v.im| ≤ Real.pi*t/4) (n : ℕ) :
    ‖thetaReducedTerm t (n+1) v‖ ≤ (21/25:ℝ)*(686/15625:ℝ)^n := by
  have ht0 : 0 < t := by linarith
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hn2 : (n:ℝ) ≤ (n:ℝ)^2 := by
    by_cases h : n = 0
    · simp [h]
    · have h1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      nlinarith
  have he1 : -Real.pi*t*(n+1)*(n+2)/2+2*(n+1)*|v.im| ≤
      -Real.pi*t*(n+1)^2/2 := by nlinarith [mul_nonneg (by positivity : 0 ≤ (n:ℝ)+1) (sub_nonneg.mpr hv)]
  have he2 : -Real.pi*t*(n+1)^2/2 ≤ -Real.pi*t*(1+3*n)/2 := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ Real.pi*t) (sub_nonneg.mpr hn2)]
  have hexp : Real.exp (-Real.pi*t*(1+3*n)/2) =
      Real.exp (-Real.pi*t/2)*(Real.exp (-Real.pi*t/2)^3)^n := by
    rw [← pow_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hr := exp_neg_half_pi_le ht
  calc
    ‖thetaReducedTerm t (n+1) v‖ = Real.exp (-Real.pi*t*(n+1)*(n+2)/2)*‖oddSineFactor (n+1) v‖ := by
      simp only [thetaReducedTerm,norm_mul,thetaSign_norm,one_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Nat.cast_add,Nat.cast_one]
      ring_nf
    _ ≤ Real.exp (-Real.pi*t*(n+1)*(n+2)/2)*
        ((2*n+3)*Real.exp (2*(n+1)*|v.im|)) := by
      convert
        mul_le_mul_of_nonneg_left (oddSineFactor_norm_le (n+1) v)
          (Real.exp_nonneg (-Real.pi*t*(n+1)*(n+2)/2)) using 1
      push_cast
      ring
    _ = (2*n+3)*Real.exp (-Real.pi*t*(n+1)*(n+2)/2+2*(n+1)*|v.im|) := by
      rw [Real.exp_add]
      ring
    _ ≤ (3*2^n)*Real.exp (-Real.pi*t*(1+3*n)/2) := by
      exact mul_le_mul (odd_factor_nat_bound n) (Real.exp_le_exp.mpr (he1.trans he2))
        (Real.exp_nonneg _) (by positivity)
    _ ≤ (3*2^n)*((7/25)*((7/25)^3)^n) := by
      rw [hexp]
      gcongr
    _ = (21/25:ℝ)*(686/15625:ℝ)^n := by
      rw [show (686/15625:ℝ) = 2*(7/25)^3 by norm_num, mul_pow]
      ring

theorem thetaReduced_sub_one_norm_le {t : ℝ} (ht : 43/50 ≤ t) {v : ℂ}
    (hv : |v.im| ≤ Real.pi*t/4) : ‖thetaReduced t v-1‖ ≤ 9/10 := by
  have ht0 : 0 < t := by linarith
  have hs := thetaReducedTerm_summable ht0 v
  have he : thetaReduced t v-1 = ∑' n, thetaReducedTerm t (n+1) v := by
    unfold thetaReduced
    rw [← hs.sum_add_tsum_nat_add 1]
    simp [thetaReducedTerm_zero]
  rw [he]
  have hsum : Summable (fun n : ℕ => (21/25:ℝ)*(686/15625:ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(686/15625:ℝ)‖ < 1)).mul_left _
  have hs1 : Summable (fun n : ℕ => thetaReducedTerm t (n+1) v) :=
    hs.comp_injective (fun a b h => Nat.add_right_cancel h)
  have hb := norm_tsum_le_tsum_norm hs1.norm
  calc
    ‖∑' n, thetaReducedTerm t (n+1) v‖ ≤ ∑' n, ‖thetaReducedTerm t (n+1) v‖ := hb
    _ ≤ ∑' n, (21/25:ℝ)*(686/15625:ℝ)^n :=
      hs1.norm.tsum_le_tsum
        (fun n => thetaReducedTerm_strip_bound ht hv n) hsum
    _ = (21/25:ℝ)*(1-686/15625)⁻¹ := by
      rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by norm_num : ‖(686/15625:ℝ)‖ < 1)]
    _ ≤ 9/10 := by norm_num

theorem thetaReduced_ne_zero_on_strip {t : ℝ} (ht : 43/50 ≤ t) {v : ℂ}
    (hv : |v.im| ≤ Real.pi*t/4) : thetaReduced t v ≠ 0 := by
  intro h
  have hb := thetaReduced_sub_one_norm_le ht hv
  rw [h] at hb
  norm_num at hb

theorem thetaJet_zero_iff_sin_on_strip {t : ℝ} (ht : 43/50 ≤ t) {v : ℂ}
    (hv : |v.im| ≤ Real.pi*t/4) : thetaJet t 0 v = 0 ↔ Complex.sin v = 0 := by
  rw [thetaJet_eq_sin_mul_reduced,mul_eq_zero]
  exact or_iff_left (thetaReduced_ne_zero_on_strip ht hv)

end TwoAxisHelicoid
