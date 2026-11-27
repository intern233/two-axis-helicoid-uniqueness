import TwoAxisHelicoid.ThetaScaledDerivative

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet thetaQuotient

theorem thetaJet_two_quasiperiod {t : ℝ} (ht : 0 < t) (v : ℂ) :
    thetaJet t 2 (v+thetaComplexHalfPeriod t) = thetaQuasiFactor t v*
      (thetaJet t 2 v-4*I*thetaJet t 1 v-4*thetaJet t 0 v) := by
  have hl := (thetaJet_hasDerivAt ht 1 (v+thetaComplexHalfPeriod t)).comp v
    ((hasDerivAt_id v).add_const (thetaComplexHalfPeriod t))
  simp only [Function.comp_def,id_eq,mul_one] at hl
  have hr := (thetaQuasiFactor_hasDerivAt t v).mul
    ((thetaJet_hasDerivAt ht 1 v).sub ((thetaJet_hasDerivAt ht 0 v).const_mul (2*I)))
  have he : (fun z => thetaJet t 1 (z+thetaComplexHalfPeriod t)) =
      (fun z => thetaQuasiFactor t z*(thetaJet t 1 z-2*I*thetaJet t 0 z)) :=
    funext (thetaJet_one_quasiperiod ht)
  rw [he] at hl
  calc
    _ = _ := hl.unique hr
    _ = _ := by
      simp only [Pi.sub_apply]
      ring_nf
      simp only [I_sq]
      ring

theorem thetaLogSecond_period_two (t : ℝ) : Function.Periodic (thetaLogSecond t) 2 := by
  intro z
  have hv : (Real.pi*(z+2)/2:ℂ) = Real.pi*z/2+Real.pi := by ring
  simp only [thetaLogSecond,hv,thetaQuotient_add_pi]

theorem thetaLogSecond_period_half {t : ℝ} (ht : 0 < t) :
    Function.Periodic (thetaLogSecond t) (1+I*t) := by
  intro z
  have hv : (Real.pi*(z+(1+I*t))/2:ℂ) = Real.pi*z/2+thetaComplexHalfPeriod t := by
    unfold thetaComplexHalfPeriod
    ring
  by_cases hz : thetaJet t 0 (Real.pi*z/2) = 0
  · have hz' : thetaJet t 0 (Real.pi*(z+(1+I*t))/2) = 0 := by
      rw [hv,thetaJet_zero_quasiperiod ht,hz,mul_zero]
    rw [thetaLogSecond_eq_zero_of_theta_zero hz',thetaLogSecond_eq_zero_of_theta_zero hz]
  · have hq : thetaQuasiFactor t (Real.pi*z/2) ≠ 0 := Complex.exp_ne_zero _
    simp only [thetaLogSecond,hv,thetaQuotient,thetaJet_zero_quasiperiod ht,
      thetaJet_one_quasiperiod ht,thetaJet_two_quasiperiod ht]
    field_simp
    ring_nf
    simp only [I_sq]
    ring

theorem thetaLogSecond_add_lattice {t : ℝ} (ht : 0 < t) (z : ℂ)
    (l : (rhombicPeriodPair t ht).lattice) : thetaLogSecond t (z+l) = thetaLogSecond t z := by
  obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp l.property
  rw [← he]
  change thetaLogSecond t (z+((m:ℂ)*2+(n:ℂ)*(1+I*t))) = _
  have h1 := (thetaLogSecond_period_two t).zsmul m z
  have h2 := (thetaLogSecond_period_half ht).zsmul n (z+(m:ℂ)*2)
  simp only [zsmul_eq_mul] at h1 h2
  rw [← add_assoc,h2,h1]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaLogSecond_add_lattice
