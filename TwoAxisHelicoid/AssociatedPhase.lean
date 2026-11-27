import TwoAxisHelicoid.HeightFlux

namespace TwoAxisHelicoid
open Complex

theorem rotated_period_real (θ : ℝ) (P : ℂ) (hP : P.re = 0) :
    (Complex.exp ((θ:ℂ)*I)*P).re = -Real.sin θ*P.im := by
  rw [Complex.mul_re,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,hP]
  ring

/-- The period-algebra part of Appendix C.3, for any family of closed periods
with at least one nonzero imaginary component. -/
theorem associated_periods_close_iff {ι : Type*} (P : ι → ℂ)
    (hclosed : ∀ j, (P j).re = 0) (hn : ∃ j, (P j).im ≠ 0) (θ : ℝ) :
    (∀ j, (Complex.exp ((θ:ℂ)*I)*P j).re = 0) ↔ ∃ k : ℤ, θ = (k:ℝ)*Real.pi := by
  have hsin : (∀ j, (Complex.exp ((θ:ℂ)*I)*P j).re = 0) ↔ Real.sin θ = 0 := by
    constructor
    · intro h
      obtain ⟨j,hj⟩ := hn
      have he := h j
      rw [rotated_period_real θ (P j) (hclosed j)] at he
      exact neg_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hj)
    · intro h j
      rw [rotated_period_real θ (P j) (hclosed j),h]
      ring
  rw [hsin,Real.sin_eq_zero_iff]
  exact exists_congr (fun _ => eq_comm)

theorem associated_phase_eq_sign {θ : ℝ} (hθ : ∃ k : ℤ, θ = (k:ℝ)*Real.pi) :
    Complex.exp ((θ:ℂ)*I) = 1 ∨ Complex.exp ((θ:ℂ)*I) = -1 := by
  have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff.mpr
    (by obtain ⟨k,hk⟩ := hθ; exact ⟨k,hk.symm⟩)
  have hc := Real.sin_eq_zero_iff_cos_eq.mp hs
  rw [Complex.exp_ofReal_mul_I,hs]
  simp only [Complex.ofReal_zero,zero_mul,add_zero]
  rcases hc with hc | hc
  · left
    rw [hc,Complex.ofReal_one]
  · right
    rw [hc,Complex.ofReal_neg,Complex.ofReal_one]

theorem actual_height_associated_closed_iff {t c : ℝ} (ht : 0 < t) (hc : c ≠ 0) (θ : ℝ) :
    ((Complex.exp ((θ:ℂ)*I)*heightPeriodTwo t ht c (Real.pi/t-(thetaEtaExpression t).re)).re = 0 ∧
     (Complex.exp ((θ:ℂ)*I)*heightPeriodHalf t ht c (Real.pi/t-(thetaEtaExpression t).re)).re = 0) ↔
      ∃ k : ℤ, θ = (k:ℝ)*Real.pi := by
  let P : Fin 2 → ℂ := ![heightPeriodTwo t ht c (Real.pi/t-(thetaEtaExpression t).re),
    heightPeriodHalf t ht c (Real.pi/t-(thetaEtaExpression t).re)]
  have hclosed (j : Fin 2) : (P j).re = 0 := by
    fin_cases j <;> dsimp [P]
    · rw [heightPeriodTwo_closed_eq_I ht c]
      simp
    · rw [heightPeriodHalf_closed_eq_I ht c]
      simp
  have hn : ∃ j, (P j).im ≠ 0 := ⟨1,heightPeriodHalf_closed_im_ne_zero ht hc⟩
  have h := associated_periods_close_iff P hclosed hn θ
  simpa only [Fin.forall_fin_two,P,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_height_associated_closed_iff
