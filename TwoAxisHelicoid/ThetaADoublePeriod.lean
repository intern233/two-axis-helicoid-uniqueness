import TwoAxisHelicoid.ThetaQuasiPeriod
import TwoAxisHelicoid.ThetaAReality

namespace TwoAxisHelicoid
open Complex
open scoped ComplexConjugate
attribute [local irreducible] thetaJet thetaTerm thetaQuotient

theorem thetaQuasiFactor_translate_real (t a : ℝ) (v : ℂ) :
    thetaQuasiFactor t (v-Real.pi*a/2) = thetaQuasiFactor t v*exp (Real.pi*a*I) := by
  unfold thetaQuasiFactor
  rw [← Complex.exp_add]
  congr 1
  ring

theorem thetaA_complex_period {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Function.Periodic (thetaA t a) (1+I*t) := by
  intro z
  let v : ℂ := Real.pi*z/2
  let m : ℂ := Real.pi*(z-a)/2
  have hv : (Real.pi*(z+(1+I*t))/2 : ℂ) = v+thetaComplexHalfPeriod t := by
    dsimp [v, thetaComplexHalfPeriod]
    ring
  have hm : (Real.pi*(z+(1+I*t)-a)/2 : ℂ) = m+thetaComplexHalfPeriod t := by
    dsimp [m, thetaComplexHalfPeriod]
    ring
  have hmv : m = v-Real.pi*a/2 := by dsimp [m,v]; ring
  have hq : thetaQuasiFactor t v ≠ 0 := Complex.exp_ne_zero _
  by_cases hz : thetaJet t 0 v = 0
  · simp only [thetaA, hv, hm, thetaJet_zero_quasiperiod ht, hz,
      mul_zero, div_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, v]
  · have hratio : thetaJet t 0 (m+thetaComplexHalfPeriod t)/
        thetaJet t 0 (v+thetaComplexHalfPeriod t) =
        exp (Real.pi*a*I)*(thetaJet t 0 m/thetaJet t 0 v) := by
      rw [thetaJet_zero_quasiperiod ht, thetaJet_zero_quasiperiod ht, hmv,
        thetaQuasiFactor_translate_real]
      field_simp
    have hunit : exp (Real.pi*a*I)^2*exp (-2*(a-1)*Real.pi*I) = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      have he : ((2 : ℕ) : ℂ)*(Real.pi*a*I)+ -2*(a-1)*Real.pi*I = 2*Real.pi*I := by
        push_cast
        ring
      rw [he, Complex.exp_two_pi_mul_I]
    have he (q : ℂ) : exp ((a-1)*Real.pi*(q-2*I)) =
        exp ((a-1)*Real.pi*q)*exp (-2*(a-1)*Real.pi*I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    simp only [thetaA, hv, hm, hratio, thetaQuotient_one_quasiperiod ht hz, he, mul_pow]
    change _ = _
    calc
      _ = (((Real.pi*thetaJet t 1 0)/(2*thetaJet t 0 (Real.pi*a/2)))^2*
          (thetaJet t 0 m/thetaJet t 0 v)^2*exp ((a-1)*Real.pi*thetaQuotient t 1 v))*
          (exp (Real.pi*a*I)^2*exp (-2*(a-1)*Real.pi*I)) := by ring
      _ = _ := by rw [hunit, mul_one]

theorem thetaA_midline_add_one {t : ℝ} (ht : 0 < t) (a x : ℝ) :
    thetaA t a (((x+1 : ℝ) : ℂ)+I*((t/2 : ℝ) : ℂ)) =
      conj (thetaA t a ((x : ℂ)+I*((t/2 : ℝ) : ℂ))) := by
  have harg : (((x+1 : ℝ) : ℂ)+I*((t/2 : ℝ) : ℂ)) =
      conj ((x : ℂ)+I*((t/2 : ℝ) : ℂ))+(1+I*t) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [harg, thetaA_complex_period ht a, thetaA_conj]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaA_complex_period
