import TwoAxisHelicoid.ThetaZeroSet

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet

theorem thetaJet_one_at_zero_eq_reduced (t : ℝ) :
    thetaJet t 1 0 = thetaReduced t 0 := by
  unfold thetaJet thetaReduced
  apply tsum_congr
  intro n
  simp only [thetaTerm,thetaReducedTerm,sineJet_one,mul_zero,Complex.cos_zero,
    pow_one,oddSineFactor,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

theorem thetaJet_one_at_zero_ne_zero {t : ℝ} (ht : 43/50 ≤ t) : thetaJet t 1 0 ≠ 0 := by
  rw [thetaJet_one_at_zero_eq_reduced]
  apply thetaReduced_ne_zero_on_strip ht
  have ht0 : 0 < t := by linarith
  simp only [Complex.zero_im,abs_zero]
  positivity

theorem theta_simple_periodic_pi (t : ℝ) :
    Function.Periodic (fun v : ℂ => thetaJet t 0 v = 0 ∧ thetaJet t 1 v ≠ 0) Real.pi := by
  intro v
  apply propext
  dsimp only
  simp only [thetaJet_add_pi,neg_eq_zero,ne_eq]

theorem theta_simple_periodic_half {t : ℝ} (ht : 0 < t) :
    Function.Periodic (fun v : ℂ => thetaJet t 0 v = 0 ∧ thetaJet t 1 v ≠ 0)
      (thetaComplexHalfPeriod t) := by
  intro v
  apply propext
  dsimp only
  rw [thetaJet_zero_quasiperiod ht,thetaJet_one_quasiperiod ht]
  have hq : thetaQuasiFactor t v ≠ 0 := Complex.exp_ne_zero _
  constructor
  · rintro ⟨h0,h1⟩
    have hz := (mul_eq_zero.mp h0).resolve_left hq
    refine ⟨hz,?_⟩
    rw [hz,mul_zero,sub_zero] at h1
    exact (mul_ne_zero_iff.mp h1).2
  · rintro ⟨h0,h1⟩
    simp only [h0,mul_zero,sub_zero]
    exact ⟨trivial,mul_ne_zero hq h1⟩

theorem thetaJet_simple_at_every_zero {t : ℝ} (ht : 43/50 ≤ t) {v : ℂ}
    (hv : thetaJet t 0 v = 0) : thetaJet t 1 v ≠ 0 := by
  have ht0 : 0 < t := by linarith
  obtain ⟨m,n,he⟩ := (thetaJet_zero_iff_period_span ht v).mp hv
  have h1 := (theta_simple_periodic_half ht0).zsmul n ((m:ℂ)*Real.pi)
  have h2 := (theta_simple_periodic_pi t).zsmul_eq m
  simp only [zsmul_eq_mul] at h1 h2
  have hp : thetaJet t 0 v = 0 ∧ thetaJet t 1 v ≠ 0 := by
    rw [he,h1,h2]
    exact ⟨thetaJet_zero_at_zero t,thetaJet_one_at_zero_ne_zero ht⟩
  exact hp.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaJet_simple_at_every_zero
