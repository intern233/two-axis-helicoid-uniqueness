import TwoAxisHelicoid.ThetaBilateral
import TwoAxisHelicoid.ThetaPeriod

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaJet thetaTerm thetaBilateralTerm

theorem thetaJet_zero_quasiperiod {t : ℝ} (ht : 0 < t) (v : ℂ) :
    thetaJet t 0 (v+thetaComplexHalfPeriod t) = thetaQuasiFactor t v*thetaJet t 0 v := by
  have hs : (∑' n : ℤ, thetaBilateralTerm t n (v+thetaComplexHalfPeriod t)) =
      thetaQuasiFactor t v*(∑' n : ℤ, thetaBilateralTerm t n v) := by
    simp_rw [thetaBilateralTerm_shift]
    rw [tsum_mul_left]
    congr 1
    exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => thetaBilateralTerm t n v)
  rw [thetaBilateral_sum ht, thetaBilateral_sum ht] at hs
  apply mul_left_cancel₀ (show (2 : ℂ)*I ≠ 0 by simp)
  calc
    _ = thetaQuasiFactor t v*((2*I)*thetaJet t 0 v) := hs
    _ = _ := by ring

theorem thetaQuasiFactor_hasDerivAt (t : ℝ) (v : ℂ) :
    HasDerivAt (thetaQuasiFactor t) (-2*I*thetaQuasiFactor t v) v := by
  have h := (((hasDerivAt_id v).mul_const (2*I)).const_sub
    (Real.pi*I/2+Real.pi*t/2)).cexp
  simp only [id_eq] at h
  convert h using 1
  · funext z
    unfold thetaQuasiFactor
    congr 1
    ring
  · unfold thetaQuasiFactor
    have he : (Real.pi*I/2+Real.pi*t/2-v*(2*I) : ℂ) =
        Real.pi*I/2+Real.pi*t/2-2*v*I := by ring
    simp only [he]
    ring

theorem thetaJet_one_quasiperiod {t : ℝ} (ht : 0 < t) (v : ℂ) :
    thetaJet t 1 (v+thetaComplexHalfPeriod t) =
      thetaQuasiFactor t v*(thetaJet t 1 v-2*I*thetaJet t 0 v) := by
  have hl := (thetaJet_hasDerivAt ht 0 (v+thetaComplexHalfPeriod t)).comp v
    ((hasDerivAt_id v).add_const (thetaComplexHalfPeriod t))
  simp only [Function.comp_def, id_eq, mul_one, zero_add] at hl
  have hr := (thetaQuasiFactor_hasDerivAt t v).mul (thetaJet_hasDerivAt ht 0 v)
  have he : (fun z => thetaJet t 0 (z+thetaComplexHalfPeriod t)) =
      (fun z => thetaQuasiFactor t z*thetaJet t 0 z) := funext (thetaJet_zero_quasiperiod ht)
  rw [he] at hl
  have hd := hl.unique hr
  calc
    _ = _ := hd
    _ = _ := by ring

theorem thetaQuotient_one_quasiperiod {t : ℝ} (ht : 0 < t) {v : ℂ}
    (hv : thetaJet t 0 v ≠ 0) :
    thetaQuotient t 1 (v+thetaComplexHalfPeriod t) = thetaQuotient t 1 v-2*I := by
  have hq : thetaQuasiFactor t v ≠ 0 := Complex.exp_ne_zero _
  unfold thetaQuotient
  rw [thetaJet_zero_quasiperiod ht, thetaJet_one_quasiperiod ht]
  field_simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaQuotient_one_quasiperiod
