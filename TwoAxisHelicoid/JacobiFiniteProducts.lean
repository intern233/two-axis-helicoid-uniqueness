import TwoAxisHelicoid.ProductPerturbationBounds

namespace TwoAxisHelicoid
open Complex
set_option maxHeartbeats 800000
attribute [local irreducible] jacobiFactorProduct

noncomputable def jacobiFiniteProduct (Q x : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, (1-Q^(n+1)*x)

theorem jacobiFactorProduct_split {Q : ℂ} (hQ : ‖Q‖ < 1) (x : ℂ) (N : ℕ) :
    jacobiFactorProduct Q x = jacobiFiniteProduct Q x N*jacobiFactorProduct Q (Q^N*x) := by
  induction N with
  | zero => simp [jacobiFiniteProduct]
  | succ n ih =>
    have he : Q*(Q^n*x) = Q^(n+1)*x := by ring
    have hs := jacobiFactorProduct_shift hQ (Q^n*x)
    rw [he] at hs
    rw [ih, ← hs]
    simp only [jacobiFiniteProduct, Finset.prod_range_succ]
    ring

theorem jacobiFactorProduct_tail_estimate {Q : ℂ} (hQ : ‖Q‖ < 1) (x : ℂ) (N : ℕ) :
    ‖jacobiFactorProduct Q x-jacobiFiniteProduct Q x N‖ ≤
      ‖jacobiFiniteProduct Q x N‖*
        (Real.exp (‖Q^(N+1)*x‖/(1-‖Q‖))-1) := by
  have h := jacobiFactorProduct_sub_one_norm_le hQ (Q^N*x)
  have he : ‖Q‖*‖Q^N*x‖ = ‖Q^(N+1)*x‖ := by
    rw [← norm_mul]
    congr 1
    ring
  rw [he] at h
  rw [jacobiFactorProduct_split hQ x N]
  have he' : jacobiFiniteProduct Q x N*jacobiFactorProduct Q (Q^N*x)-jacobiFiniteProduct Q x N =
      jacobiFiniteProduct Q x N*(jacobiFactorProduct Q (Q^N*x)-1) := by ring
  rw [he', norm_mul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- A rational checker may supply `σ`, `τ`, and `M`; this theorem connects those
finite norm bounds to the actual infinite product. -/
theorem jacobiFactorProduct_finite_error {Q x : ℂ} {N : ℕ} {σ τ M : ℝ}
    (hσ : ‖Q‖ ≤ σ) (hσ1 : σ < 1) (hτ : ‖Q^(N+1)*x‖ ≤ τ)
    (hM : ‖jacobiFiniteProduct Q x N‖ ≤ M) (hsmall : τ/(1-σ) ≤ 1) :
    ‖jacobiFactorProduct Q x-jacobiFiniteProduct Q x N‖ ≤ 2*M*τ/(1-σ) := by
  have hQ : ‖Q‖ < 1 := hσ.trans_lt hσ1
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans hτ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hd0 : 0 < 1-σ := sub_pos.mpr hσ1
  have hd : 1-σ ≤ 1-‖Q‖ := by linarith
  have hδ : ‖Q^(N+1)*x‖/(1-‖Q‖) ≤ τ/(1-σ) :=
    (div_le_div_of_nonneg_right hτ (sub_pos.mpr hQ).le).trans
      (div_le_div_of_nonneg_left hτ0 hd0 hd)
  have he := (le_abs_self (Real.exp (τ/(1-σ))-1)).trans
    (Real.abs_exp_sub_one_le (by rw [abs_of_nonneg (div_nonneg hτ0 hd0.le)]; exact hsmall))
  rw [abs_of_nonneg (div_nonneg hτ0 hd0.le)] at he
  rw [← mul_div_assoc] at he
  have hE : Real.exp (‖Q^(N+1)*x‖/(1-‖Q‖))-1 ≤ 2*τ/(1-σ) := by
    have hm := Real.exp_le_exp.mpr hδ
    linarith
  have hE0 : 0 ≤ Real.exp (‖Q^(N+1)*x‖/(1-‖Q‖))-1 := by
    apply sub_nonneg.mpr
    exact Real.one_le_exp_iff.mpr (div_nonneg (norm_nonneg _) (sub_pos.mpr hQ).le)
  have hm := mul_le_mul hM hE hE0 hM0
  have h := jacobiFactorProduct_tail_estimate hQ x N
  calc
    _ ≤ M*(2*τ/(1-σ)) := h.trans hm
    _ = _ := by ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.jacobiFactorProduct_finite_error
