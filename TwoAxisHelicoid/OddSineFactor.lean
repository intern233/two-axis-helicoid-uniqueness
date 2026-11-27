import TwoAxisHelicoid.ThetaBasic

namespace TwoAxisHelicoid
open Complex

/-- The entire quotient of an odd sine multiple by sine, including at its zeros. -/
noncomputable def oddSineFactor (n : ℕ) (v : ℂ) : ℂ :=
  1+2*∑ k ∈ Finset.range n, Complex.cos (2*((k:ℂ)+1)*v)

theorem sin_odd_multiple (n : ℕ) (v : ℂ) :
    Complex.sin ((2*n+1:ℂ)*v) = Complex.sin v*oddSineFactor n v := by
  induction n with
  | zero => simp [oddSineFactor]
  | succ n ih =>
    have h := Complex.sin_sub_sin ((2*(n+1)+1:ℂ)*v) ((2*n+1:ℂ)*v)
    have h1 : (((2*(n+1)+1:ℂ)*v)-((2*n+1:ℂ)*v))/2 = v := by ring
    have h2 : (((2*(n+1)+1:ℂ)*v)+((2*n+1:ℂ)*v))/2 = 2*(n+1)*v := by ring
    rw [h1,h2,ih] at h
    simp only [oddSineFactor, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at h ⊢
    linear_combination h

theorem oddSineFactor_norm_le (n : ℕ) (v : ℂ) :
    ‖oddSineFactor n v‖ ≤ (2*n+1:ℝ)*Real.exp (2*n*|v.im|) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have he : (1:ℝ) ≤ Real.exp (2*n*|v.im|) := Real.one_le_exp (by positivity)
  have hb : ∀ k ∈ Finset.range n,
      ‖Complex.cos (2*((k:ℂ)+1)*v)‖ ≤ Real.exp (2*n*|v.im|) := by
    intro k hk
    have hk' : (k:ℝ)+1 ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
    have harg : |(2*((k:ℂ)+1)*v).im| = 2*((k:ℝ)+1)*|v.im| := by
      have hc : (2*((k:ℂ)+1)) = ((2*((k:ℝ)+1):ℝ):ℂ) := by push_cast; rfl
      rw [hc]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)*((k:ℝ)+1))]
    have hh := sineJet_norm_le 1 (2*((k:ℂ)+1)*v)
    rw [sineJet_one,harg] at hh
    exact hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk' (by norm_num)) (abs_nonneg _)))
  calc
    ‖oddSineFactor n v‖ ≤ 1+2*‖∑ k ∈ Finset.range n, Complex.cos (2*((k:ℂ)+1)*v)‖ := by
      simpa only [oddSineFactor, norm_one, norm_mul, norm_ofNat] using
        norm_add_le (1:ℂ) (2*∑ k ∈ Finset.range n, Complex.cos (2*((k:ℂ)+1)*v))
    _ ≤ 1+2*∑ k ∈ Finset.range n, ‖Complex.cos (2*((k:ℂ)+1)*v)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ 1+2*((n:ℝ)*Real.exp (2*n*|v.im|)) := by
      gcongr
      simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using Finset.sum_le_sum hb
    _ ≤ (2*n+1:ℝ)*Real.exp (2*n*|v.im|) := by nlinarith

end TwoAxisHelicoid
