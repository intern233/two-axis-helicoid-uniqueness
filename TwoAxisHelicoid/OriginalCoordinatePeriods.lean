import TwoAxisHelicoid.OriginalPeriodBridge
import TwoAxisHelicoid.CoordinateDataSymmetry

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped ComplexConjugate Interval
attribute [local irreducible] thetaA coordinateData

noncomputable def originalCoordinatePeriod (t a c : ℝ) (ht : 0 < t) (j : Fin 3) : ℂ :=
  ((1-I*t)/2)*(∫ s : ℝ in (-1)..1, coordinateData t a c ht (originalPeriodPath t s) j)

noncomputable def conjugateCoordinatePeriod (t a c : ℝ) (ht : 0 < t) (j : Fin 3) : ℂ :=
  ((1+I*t)/2)*(∫ s : ℝ in (-1)..1, coordinateData t a c ht (conj (originalPeriodPath t s)) j)

theorem thetaA_originalPath_neg (t a s : ℝ) :
    thetaA t a (-originalPeriodPath t s) = thetaA t a (originalPeriodPath t (-s)) := by
  have he : -originalPeriodPath t s = originalPeriodPath t (-s)+2 := by
    unfold originalPeriodPath
    push_cast
    ring
  rw [he,thetaA_periodic t a]

theorem originalPath_kernel_integrable {t : ℝ} (ht : 0 < t) (a : ℝ) :
    IntervalIntegrable (fun s : ℝ => thetaA t a (originalPeriodPath t s)) volume (-1) 1 := by
  apply ContinuousOn.intervalIntegrable
  apply (thetaA_holomorphic_original_rectangle ht a).continuousOn.comp
    (by unfold originalPeriodPath; fun_prop)
  intro s hs
  exact originalPeriodPath_mem_rectangle ht (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hs)

theorem originalPath_negative_kernel_integral (t a : ℝ) :
    (∫ s : ℝ in (-1)..1, thetaA t a (-originalPeriodPath t s)) =
      ∫ s : ℝ in (-1)..1, thetaA t a (originalPeriodPath t s) := by
  simp_rw [thetaA_originalPath_neg]
  simpa using intervalIntegral.integral_comp_neg
    (f := fun s : ℝ => thetaA t a (originalPeriodPath t s)) (a := -1) (b := 1)

theorem originalCoordinatePeriod_horizontal {t a c : ℝ} (ht : 0 < t) :
    originalCoordinatePeriod t a c ht 0 = -(c:ℂ)*originalSlopingPeriod t a ∧
    originalCoordinatePeriod t a c ht 1 = 0 := by
  have hA := originalPath_kernel_integrable ht a
  have hN : IntervalIntegrable (fun s : ℝ => thetaA t a (-originalPeriodPath t s)) volume (-1) 1 := by
    simp_rw [thetaA_originalPath_neg]
    simpa using ((IntervalIntegrable.iff_comp_neg (by finiteness)).mp hA).symm
  constructor
  · unfold originalCoordinatePeriod coordinateData originalSlopingPeriod
    simp only [Matrix.cons_val_zero]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hN hA,
      originalPath_negative_kernel_integral]
    ring
  · unfold originalCoordinatePeriod coordinateData
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub hA hN,
      originalPath_negative_kernel_integral,sub_self,mul_zero,mul_zero]

theorem conjugateCoordinatePeriod_horizontal {t a c : ℝ} (ht : 0 < t) :
    conjugateCoordinatePeriod t a c ht 0 = conj (originalCoordinatePeriod t a c ht 0) ∧
    conjugateCoordinatePeriod t a c ht 1 = -conj (originalCoordinatePeriod t a c ht 1) := by
  constructor
  · unfold conjugateCoordinatePeriod originalCoordinatePeriod
    simp_rw [coordinateData_conj ht]
    simp only [Matrix.cons_val_zero,intervalIntegral.intervalIntegral_conj,map_mul,map_div₀,
      map_sub,map_one,map_ofNat,Complex.conj_I,Complex.conj_ofReal,neg_mul,sub_neg_eq_add]
  · unfold conjugateCoordinatePeriod originalCoordinatePeriod
    simp_rw [coordinateData_conj ht]
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero,intervalIntegral.integral_neg,
      intervalIntegral.intervalIntegral_conj,map_mul,map_div₀,map_sub,map_one,map_ofNat,
      Complex.conj_I,Complex.conj_ofReal,neg_mul,sub_neg_eq_add,mul_neg]

theorem original_horizontal_generators_close_iff {t a c : ℝ} (ht : 0 < t) (hc : c ≠ 0) :
    ((originalCoordinatePeriod t a c ht 0).re = 0 ∧
      (originalCoordinatePeriod t a c ht 1).re = 0 ∧
      (conjugateCoordinatePeriod t a c ht 0).re = 0 ∧
      (conjugateCoordinatePeriod t a c ht 1).re = 0) ↔
        thetaHorizontalPeriod t a = 0 := by
  rw [(conjugateCoordinatePeriod_horizontal ht).1,(conjugateCoordinatePeriod_horizontal ht).2,
    (originalCoordinatePeriod_horizontal ht).1,(originalCoordinatePeriod_horizontal ht).2,
    map_zero,neg_zero]
  simp only [Complex.conj_re,Complex.zero_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,neg_zero,zero_mul,sub_zero,
    originalSlopingPeriod_re_eq_horizontal ht a,mul_eq_zero,neg_eq_zero,hc,false_or,
    and_true,true_and,and_self]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.original_horizontal_generators_close_iff
