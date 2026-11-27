import TwoAxisHelicoid.OriginalTimeIntegral
import TwoAxisHelicoid.EllipticPeriodDerivative

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaA thetaLt thetaLz

theorem originalPath_linear_spatial_identity {t : ℝ} (ht : 0 < t) (a : ℝ) :
    (∫ s : ℝ in (-1)..1, thetaA t a (originalPeriodPath t s))+
      ((1-I*t)/2)*(∫ s : ℝ in (-1)..1,
        (s : ℂ)*deriv (thetaA t a) (originalPeriodPath t s)) =
      2*thetaA t a (originalPeriodPath t (-1)) := by
  let A := fun s : ℝ => thetaA t a (originalPeriodPath t s)
  let D := fun s : ℝ => deriv (thetaA t a) (originalPeriodPath t s)
  let q : ℂ := (1-I*t)/2
  have hIA : IntervalIntegrable A volume (-1) 1 := originalPath_kernel_integrable ht a
  have hID : IntervalIntegrable (fun s : ℝ => (s : ℂ)*D s) volume (-1) 1 :=
    (Complex.continuous_ofReal.continuousOn.mul (originalPath_derivative_continuousOn ht a)).intervalIntegrable_of_Icc
      (by norm_num)
  have hd (s : ℝ) (hs : s ∈ uIcc (-1 : ℝ) 1) :
      HasDerivAt (fun r : ℝ => (r : ℂ)*A r) (A s+q*((s : ℂ)*D s)) s := by
    have hreg := originalPath_regular ht
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)
    have hA := (thetaA_differentiableAt ht a hreg).hasDerivAt.comp s
      (originalPeriodPath_hasDerivAt t s)
    convert ((hasDerivAt_id s).ofReal_comp).mul hA using 1
    · rfl
    · dsimp [A,D,q]
      simp only [one_mul]
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hIA.add (hID.const_mul q))
  rw [intervalIntegral.integral_add hIA (hID.const_mul q),intervalIntegral.integral_const_mul] at h
  have he : A 1 = A (-1) := originalPath_kernel_endpoints ht a
  simp only [Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_one_mul,he] at h
  change (∫ s : ℝ in (-1)..1, A s)+q*(∫ s : ℝ in (-1)..1, (s : ℂ)*D s) = 2*A (-1)
  linear_combination h

theorem originalPath_fixed_time_continuousOn {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun s : ℝ => thetaA t a (originalPeriodPath t s)*
      thetaLt t a (originalPeriodPath t s)) (Icc (-1 : ℝ) 1) := by
  have hz : ContinuousOn (originalPeriodPath t) (Icc (-1 : ℝ) 1) := by
    unfold originalPeriodPath
    fun_prop
  have hc := thetaAtMidline_comp_continuousOn (u := fun _ : ℝ => t)
    (b := fun _ : ℝ => a) continuousOn_const continuousOn_const hz
    (fun _ _ => ht)
    (fun _ _ => theta_vertical_denominator ht ha.1 (by linarith [ha.2]))
    (fun _ hs => originalPath_regular ht hs)
    (fun _ hs => originalPath_shift_regular ht ha hs)
    (fun _ _ => thetaJet_one_at_zero_ne_zero_of_pos ht)
  have hD := originalPath_derivative_continuousOn ht a
  apply (hc.sub (continuousOn_const.mul hD : ContinuousOn
    (fun s : ℝ => (I/2)*deriv (thetaA t a) (originalPeriodPath t s)) (Icc (-1 : ℝ) 1))).congr
  intro s hs
  change thetaA t a (originalPeriodPath t s)*thetaLt t a (originalPeriodPath t s) =
    thetaAtMidline t a (originalPeriodPath t s)-(I/2)*deriv (thetaA t a) (originalPeriodPath t s)
  rw [thetaA_spatial_deriv ht a
    (theta_vertical_denominator ht ha.1 (by linarith [ha.2]))
    (originalPath_regular ht hs) (originalPath_shift_regular ht ha hs)]
  unfold thetaAtMidline
  ring

theorem originalSlopingPeriod_t_hasDerivAt_moving_endpoint {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => originalSlopingPeriod r a)
      (slopingIntegral t (fun z => thetaA t a z*thetaLt t a z)-
        I*thetaA t a (originalPeriodPath t (-1))) t := by
  let z := originalPeriodPath t
  let D := fun s : ℝ => deriv (thetaA t a) (z s)
  have hF : IntervalIntegrable (fun s : ℝ => thetaA t a (z s)*thetaLt t a (z s)) volume (-1) 1 :=
    (originalPath_fixed_time_continuousOn ht ha).intervalIntegrable_of_Icc (by norm_num)
  have hD : IntervalIntegrable (fun s : ℝ => (s : ℂ)*D s) volume (-1) 1 :=
    (Complex.continuous_ofReal.continuousOn.mul (originalPath_derivative_continuousOn ht a)).intervalIntegrable_of_Icc
      (by norm_num)
  have he (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) :
      originalTimeIntegrand t a s = thetaA t a (z s)*thetaLt t a (z s)-(I/2)*((s : ℂ)*D s) := by
    dsimp [D]
    rw [thetaA_spatial_deriv ht a
      (theta_vertical_denominator ht ha.1 (by linarith [ha.2]))
      (originalPath_regular ht hs) (originalPath_shift_regular ht ha hs)]
    unfold originalTimeIntegrand
    dsimp [z]
    ring
  have htime : (∫ s : ℝ in (-1)..1, originalTimeIntegrand t a s) =
      (∫ s : ℝ in (-1)..1, thetaA t a (z s)*thetaLt t a (z s))-
        (I/2)*(∫ s : ℝ in (-1)..1, (s : ℂ)*D s) := by
    calc
      _ = ∫ s : ℝ in (-1)..1, thetaA t a (z s)*thetaLt t a (z s)-(I/2)*((s : ℂ)*D s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact he s (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)
      _ = _ := by
        rw [intervalIntegral.integral_sub hF (hD.const_mul (I/2)),intervalIntegral.integral_const_mul]
  have hd := originalSlopingPeriod_t_hasDerivAt_raw ht ha
  rw [htime] at hd
  have hline := originalPath_linear_spatial_identity ht a
  convert hd using 1
  unfold slopingIntegral
  dsimp [D,z]
  linear_combination (I/2)*hline

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalSlopingPeriod_t_hasDerivAt_moving_endpoint
