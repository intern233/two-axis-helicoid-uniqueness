import TwoAxisHelicoid.OriginalPeriodAnalytic
import TwoAxisHelicoid.SlopingIntegralBridge

namespace TwoAxisHelicoid
open Complex Set MeasureTheory
open scoped Interval
attribute [local irreducible] thetaJet thetaA

theorem originalPeriodPath_hasDerivAt (t s : ℝ) :
    HasDerivAt (originalPeriodPath t) ((1-I*t)/2) s := by
  convert ((((hasDerivAt_id s).ofReal_comp).mul_const (1-I*t)).div_const 2).const_add (-1 : ℂ) using 1
  · rfl
  · simp

theorem originalPath_shift_regular {t a s : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (-1 : ℝ) 1) :
    thetaJet t 0 (Real.pi*(originalPeriodPath t s-a)/2) ≠ 0 := by
  apply mt (thetaJet_zero_iff_rhombic_lattice_of_pos ht _).mp
  intro hmem
  obtain ⟨m,n,hr,hi⟩ := (rhombic_mem_lattice_iff ht _).mp hmem
  have him : (originalPeriodPath t s-(a : ℂ)).im = -(s*t)/2 := by
    simp [originalPeriodPath,Complex.mul_re,Complex.mul_im]
  rw [him] at hi
  have hnreal : (n : ℝ) = -s/2 := by
    apply mul_right_cancel₀ ht.ne'
    nlinarith [hi]
  have hnlo : (-1 : ℤ) < n := by
    exact_mod_cast (show (-1 : ℝ) < n by linarith [hs.2])
  have hnhi : n < (1 : ℤ) := by
    exact_mod_cast (show (n : ℝ) < 1 by linarith [hs.1])
  have hn : n = 0 := by omega
  have hs0 : s = 0 := by simp only [hn,Int.cast_zero] at hnreal; linarith
  norm_num [originalPeriodPath,hs0,hn] at hr
  have hmlo : (-1 : ℤ) < m := by
    exact_mod_cast (show (-1 : ℝ) < m by linarith [ha.2])
  have hmhi : m < (0 : ℤ) := by
    exact_mod_cast (show (m : ℝ) < 0 by linarith [ha.1])
  omega

theorem originalPath_kernel_endpoints {t : ℝ} (ht : 0 < t) (a : ℝ) :
    thetaA t a (originalPeriodPath t 1) = thetaA t a (originalPeriodPath t (-1)) := by
  have he : originalPeriodPath t 1+(1+I*t) = originalPeriodPath t (-1)+2 := by
    unfold originalPeriodPath
    push_cast
    ring
  have hp := thetaA_complex_period ht a (originalPeriodPath t 1)
  rw [he,thetaA_periodic t a] at hp
  exact hp.symm

theorem originalPath_derivative_continuousOn {t : ℝ} (ht : 0 < t) (a : ℝ) :
    ContinuousOn (fun s : ℝ => deriv (thetaA t a) (originalPeriodPath t s))
      (Icc (-1 : ℝ) 1) := by
  apply (thetaA_deriv_continuousOn ht a).comp (by unfold originalPeriodPath; fun_prop)
  intro s hs
  exact originalPath_regular ht hs

theorem originalPath_spatial_derivative_integral_zero {t : ℝ} (ht : 0 < t) (a : ℝ) :
    slopingIntegral t (deriv (thetaA t a)) = 0 := by
  have hc := originalPath_derivative_continuousOn ht a
  have hi := (hc.intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1) (μ := volume)).const_mul ((1-I*t)/2)
  have hd (s : ℝ) (hs : s ∈ uIcc (-1 : ℝ) 1) :
      HasDerivAt (fun r : ℝ => thetaA t a (originalPeriodPath t r))
        (((1-I*t)/2)*deriv (thetaA t a) (originalPeriodPath t s)) s := by
    have hreg := originalPath_regular ht (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs)
    convert (thetaA_differentiableAt ht a hreg).hasDerivAt.comp s
      (originalPeriodPath_hasDerivAt t s) using 1
    · rfl
    · ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul,originalPath_kernel_endpoints ht a,sub_self] at h
  exact h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.originalPath_shift_regular
#print axioms TwoAxisHelicoid.originalPath_spatial_derivative_integral_zero
