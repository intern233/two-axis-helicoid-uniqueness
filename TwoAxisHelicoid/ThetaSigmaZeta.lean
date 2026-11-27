import TwoAxisHelicoid.ThetaWeierstrassIdentity
import TwoAxisHelicoid.ThetaParity

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet thetaScaledJet thetaLogSecond

/-- The normalized sigma function given by the manuscript's theta formula. -/
noncomputable def thetaSigma (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (thetaEtaExpression t*z^2/2)*thetaScaledJet t 0 z/thetaScaledJet t 1 0

/-- Its logarithmic derivative away from the lattice. -/
noncomputable def thetaZeta (t : ℝ) (z : ℂ) : ℂ :=
  thetaScaledJet t 1 z/thetaScaledJet t 0 z+thetaEtaExpression t*z

theorem thetaSigma_hasDerivAt {t : ℝ} (ht : 0 < t) (z : ℂ) :
    HasDerivAt (thetaSigma t)
      (Complex.exp (thetaEtaExpression t*z^2/2)*
        (thetaScaledJet t 1 z+thetaEtaExpression t*z*thetaScaledJet t 0 z)/thetaScaledJet t 1 0) z := by
  have he := ((((hasDerivAt_id z).pow 2).const_mul (thetaEtaExpression t)).div_const 2).cexp
  have hd := (he.mul (thetaScaledJet_hasDerivAt ht 0 z)).div_const (thetaScaledJet t 1 0)
  convert hd using 1
  · rfl
  · simp only [Pi.pow_apply,id_eq]
    ring

theorem thetaSigma_analyticAt {t : ℝ} (ht : 0 < t) (z : ℂ) : AnalyticAt ℂ (thetaSigma t) z :=
  (show Differentiable ℂ (thetaSigma t) from
    fun w => (thetaSigma_hasDerivAt ht w).differentiableAt).analyticAt z

theorem thetaSigma_zero (t : ℝ) : thetaSigma t 0 = 0 := by
  simp [thetaSigma,thetaScaledJet_zero_at_zero]

theorem thetaSigma_hasDerivAt_zero {t : ℝ} (ht : 43/50 ≤ t) : HasDerivAt (thetaSigma t) 1 0 := by
  have ht0 : 0 < t := by linarith
  simpa [thetaScaledJet_zero_at_zero,thetaScaledJet_one_ne_zero ht] using thetaSigma_hasDerivAt ht0 0

theorem thetaSigma_zero_iff_lattice {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) (z : ℂ) :
    thetaSigma t z = 0 ↔ z ∈ (rhombicPeriodPair t ht0).lattice := by
  rw [thetaSigma,div_eq_zero_iff,mul_eq_zero]
  simp only [Complex.exp_ne_zero,false_or,thetaScaledJet_one_ne_zero ht,or_false]
  exact thetaScaledJet_zero_iff_lattice ht ht0 z

theorem thetaZeta_hasDerivAt_log {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : thetaScaledJet t 0 z ≠ 0) :
    HasDerivAt (thetaZeta t) (-thetaLogSecond t z+thetaEtaExpression t) z := by
  have hd := ((thetaScaledJet_hasDerivAt ht 1 z).div (thetaScaledJet_hasDerivAt ht 0 z) hz).add
    ((hasDerivAt_id z).const_mul (thetaEtaExpression t))
  convert hd using 1
  · rfl
  · rw [thetaLogSecond_scaled]
    simp only [mul_one]
    field_simp
    ring

theorem thetaZeta_hasDerivAt {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    HasDerivAt (thetaZeta t) (-(rhombicPeriodPair t ht0).weierstrassP z) z := by
  have hd := thetaZeta_hasDerivAt_log ht0 (mt (thetaScaledJet_zero_iff_lattice ht ht0 z).mp hz)
  rw [thetaLogSecond_eq_weierstrassP_add_eta ht ht0 hz] at hd
  simpa only [neg_add,neg_add_cancel_right] using hd

theorem thetaSigma_hasDerivAt_zeta {t : ℝ} (ht : 43/50 ≤ t) (ht0 : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht0).lattice) :
    HasDerivAt (thetaSigma t) (thetaZeta t z*thetaSigma t z) z := by
  have hn := mt (thetaScaledJet_zero_iff_lattice ht ht0 z).mp hz
  have h1 := thetaScaledJet_one_ne_zero ht
  convert thetaSigma_hasDerivAt ht0 z using 1
  unfold thetaZeta thetaSigma
  field_simp

theorem thetaSigma_neg (t : ℝ) (z : ℂ) : thetaSigma t (-z) = -thetaSigma t z := by
  simp [thetaSigma,thetaScaledJet_neg,neg_div]

theorem thetaZeta_neg (t : ℝ) (z : ℂ) : thetaZeta t (-z) = -thetaZeta t z := by
  simp [thetaZeta,thetaScaledJet_neg,div_neg]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaZeta_hasDerivAt
