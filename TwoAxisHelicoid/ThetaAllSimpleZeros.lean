import TwoAxisHelicoid.ThetaReciprocal
import TwoAxisHelicoid.ThetaScaledDerivative

namespace TwoAxisHelicoid
open Complex Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaScaledJet

theorem thetaScaledJet_zero_reciprocal {t : ℝ} (ht : 0 < t) (z : ℂ) :
    thetaScaledJet t 0 z = thetaReciprocalFactor t z*thetaScaledJet (1/t) 0 (z/(I*t)) := by
  simp only [thetaScaledJet,pow_zero,one_mul]
  have harg (w : ℂ) : (Real.pi/2:ℂ)*w = Real.pi*w/2 := by ring
  simp only [harg]
  exact thetaJet_reciprocal ht z

theorem thetaScaledJet_one_ne_zero_of_pos {t : ℝ} (ht : 0 < t) : thetaScaledJet t 1 0 ≠ 0 := by
  by_cases hlarge : 43/50 ≤ t
  · exact thetaScaledJet_one_ne_zero hlarge
  · have hsmall : t < 43/50 := lt_of_not_ge hlarge
    have hinv : (43/50:ℝ) ≤ 1/t := by
      apply (le_div_iff₀ ht).mpr
      nlinarith
    have htinv := one_div_pos.mpr ht
    have hnew : HasDerivAt (thetaScaledJet (1/t) 0) (thetaScaledJet (1/t) 1 0) ((0:ℂ)/(I*t)) := by
      simpa only [zero_div] using thetaScaledJet_hasDerivAt htinv 0 0
    have hc := hnew.comp (h := fun z : ℂ => z/(I*t)) 0 ((hasDerivAt_id (0:ℂ)).div_const (I*t))
    have hm := ((thetaReciprocalFactor_differentiable t).differentiableAt (x := (0:ℂ))).hasDerivAt
    have hprod := hm.mul hc
    have he : thetaScaledJet t 0 =ᶠ[𝓝 (0:ℂ)]
        fun z => thetaReciprocalFactor t z*thetaScaledJet (1/t) 0 (z/(I*t)) :=
      Eventually.of_forall (thetaScaledJet_zero_reciprocal ht)
    have hd := (thetaScaledJet_hasDerivAt ht 0 0).unique (hprod.congr_of_eventuallyEq he)
    simp only [Function.comp_apply,zero_div,thetaScaledJet_zero_at_zero,mul_zero,zero_add] at hd
    rw [hd]
    exact mul_ne_zero (thetaReciprocalFactor_ne_zero ht 0)
      (mul_ne_zero (thetaScaledJet_one_ne_zero hinv)
        (div_ne_zero one_ne_zero (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'))))

theorem thetaJet_one_at_zero_ne_zero_of_pos {t : ℝ} (ht : 0 < t) : thetaJet t 1 0 ≠ 0 := by
  have hn := thetaScaledJet_one_ne_zero_of_pos ht
  simp only [thetaScaledJet,pow_one,mul_zero] at hn
  exact (mul_ne_zero_iff.mp hn).2

theorem thetaJet_simple_at_every_zero_of_pos {t : ℝ} (ht : 0 < t) {v : ℂ}
    (hv : thetaJet t 0 v = 0) : thetaJet t 1 v ≠ 0 := by
  obtain ⟨m,n,he⟩ := (thetaJet_zero_iff_period_span_of_pos ht v).mp hv
  have h1 := (theta_simple_periodic_half ht).zsmul n ((m:ℂ)*Real.pi)
  have h2 := (theta_simple_periodic_pi t).zsmul_eq m
  simp only [zsmul_eq_mul] at h1 h2
  have hp : thetaJet t 0 v = 0 ∧ thetaJet t 1 v ≠ 0 := by
    rw [he,h1,h2]
    exact ⟨thetaJet_zero_at_zero t,thetaJet_one_at_zero_ne_zero_of_pos ht⟩
  exact hp.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaJet_simple_at_every_zero_of_pos
