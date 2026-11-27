import TwoAxisHelicoid.ZetaHalfPeriod

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate
attribute [local irreducible] thetaJet thetaScaledJet thetaSigma thetaReduced

theorem thetaReduced_re_pos {t : ℝ} (ht : 43/50 ≤ t) (x : ℝ) :
    0 < (thetaReduced t x).re := by
  have ht0 : 0 < t := by linarith
  have hb := thetaReduced_sub_one_norm_le ht (v := (x:ℂ)) (by simp; positivity)
  have hr := Complex.abs_re_le_norm (thetaReduced t (x:ℂ)-1)
  simp only [Complex.sub_re,Complex.one_re] at hr
  have h := (abs_le.mp (hr.trans hb)).1
  linarith

theorem thetaScaledJet_real (t : ℝ) (j : ℕ) (x : ℝ) :
    (thetaScaledJet t j x).im = 0 := by
  have h := congrArg Complex.im (thetaScaledJet_conj t j (x:ℂ))
  simp only [Complex.conj_ofReal,Complex.conj_im] at h
  linarith

theorem thetaScaledJet_eq_ofReal (t : ℝ) (j : ℕ) (x : ℝ) :
    thetaScaledJet t j x = ((thetaScaledJet t j x).re:ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using thetaScaledJet_real t j x

theorem thetaSigma_real_formula (t x : ℝ) :
    thetaSigma t x = ((Real.exp ((thetaEtaExpression t).re*x^2/2)*
      (thetaScaledJet t 0 x).re/(thetaScaledJet t 1 0).re:ℝ):ℂ) := by
  have he : thetaEtaExpression t = ((thetaEtaExpression t).re:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using thetaEtaExpression_real t
  have hx : Complex.exp (thetaEtaExpression t*(x:ℂ)^2/2) =
      (Real.exp ((thetaEtaExpression t).re*x^2/2):ℂ) := by
    rw [he]
    push_cast
    rfl
  unfold thetaSigma
  have h1 : thetaScaledJet t 1 0 = ((thetaScaledJet t 1 0).re:ℂ) := by
    simpa only [Complex.ofReal_zero] using thetaScaledJet_eq_ofReal t 1 0
  rw [hx,thetaScaledJet_eq_ofReal t 0 x,h1]
  push_cast
  rfl

theorem thetaSigma_real (t x : ℝ) : (thetaSigma t x).im = 0 := by
  rw [thetaSigma_real_formula]
  rfl

theorem thetaScaledJet_one_re_pos {t : ℝ} (ht : 43/50 ≤ t) :
    0 < (thetaScaledJet t 1 0).re := by
  unfold thetaScaledJet
  simp only [pow_one,mul_zero,thetaJet_one_at_zero_eq_reduced,Complex.mul_re,
    Complex.div_ofNat_re,Complex.div_ofNat_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_div,zero_mul,sub_zero]
  exact mul_pos (by positivity) (thetaReduced_re_pos ht 0)

theorem thetaScaledJet_zero_re_pos {t : ℝ} (ht : 43/50 ≤ t) {x : ℝ}
    (hx : 0 < x) (hx2 : x < 2) : 0 < (thetaScaledJet t 0 x).re := by
  have hp0 : 0 < Real.pi*x/2 := by positivity
  have hp1 : Real.pi*x/2 < Real.pi := by nlinarith [Real.pi_pos]
  have ha : (Real.pi/2:ℂ)*(x:ℂ) = ((Real.pi*x/2:ℝ):ℂ) := by push_cast; ring
  unfold thetaScaledJet
  rw [pow_zero,one_mul,ha,thetaJet_eq_sin_mul_reduced]
  simp only [← Complex.ofReal_sin,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]
  exact mul_pos (Real.sin_pos_of_pos_of_lt_pi hp0 hp1) (thetaReduced_re_pos ht _)

theorem thetaSigma_re_pos {t : ℝ} (ht : 43/50 ≤ t) {x : ℝ}
    (hx : 0 < x) (hx2 : x < 2) : 0 < (thetaSigma t x).re := by
  rw [thetaSigma_real_formula,Complex.ofReal_re]
  exact div_pos (mul_pos (Real.exp_pos _) (thetaScaledJet_zero_re_pos ht hx hx2))
    (thetaScaledJet_one_re_pos ht)

theorem real_not_mem_rhombic_lattice {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {x : ℝ}
    (hx : 0 < x) (hx2 : x < 2) : (x:ℂ) ∉ (rhombicPeriodPair t ht0).lattice := by
  have hn : thetaSigma t x ≠ 0 := by
    intro he
    have hp := thetaSigma_re_pos ht hx hx2
    rw [he,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  exact mt (thetaSigma_zero_iff_lattice ht ht0 x).mpr hn

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaSigma_re_pos
