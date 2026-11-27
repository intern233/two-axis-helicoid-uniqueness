import TwoAxisHelicoid.PolarAnnulusIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace TwoAxisHelicoid
open Complex Real Set MeasureTheory Metric
open scoped Interval Topology

noncomputable def planeDiskImageArea (e : OpenPartialHomeomorph ℂ ℂ) (r : ℝ) : ℝ :=
  volume.real (e '' ball (0:ℂ) r)

theorem plane_disk_image_measure_finite (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ}
    (dom : closedBall (0:ℂ) r⊆e.source) : volume (e '' ball (0:ℂ) r)≠⊤ := by
  have compact := (isCompact_closedBall (0:ℂ) r).image_of_continuousOn (e.continuousOn.mono dom)
  exact (measure_mono (image_mono ball_subset_closedBall)).trans_lt compact.measure_lt_top |>.ne

/-- An upper bound for the squared diameter of a disk image bounds
its actual Lebesgue area. -/
theorem plane_disk_area_le_dist_bound (e : OpenPartialHomeomorph ℂ ℂ) {r B : ℝ} (hr : 0<r)
    (bound : ∀ z∈ball (0:ℂ) r, dist (e z) (e 0)^2≤B) : planeDiskImageArea e r≤π*B := by
  have pos : 0≤B := (sq_nonneg _).trans (bound 0 (mem_ball_self hr))
  have sub : e '' ball (0:ℂ) r⊆closedBall (e 0) (Real.sqrt B) := by
    rintro _ ⟨z,hz,rfl⟩
    exact (Real.le_sqrt (dist_nonneg) pos).mpr (bound z hz)
  apply (measureReal_mono (μ := volume) sub (isCompact_closedBall _ _).measure_lt_top.ne).trans_eq
  rw [measureReal_def,Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt pos]
  simp [mul_comm]

/-- The polar Jacobian integral on an annulus is bounded by the
difference of the two actual image areas. No differentiability or
Jacobian formula at the center of either disk is needed. -/
theorem plane_annulus_jacobian_area (e : OpenPartialHomeomorph ℂ ℂ) {r R : ℝ} (hr : 0<r) (lt : r<R)
    (dom : closedBall (0:ℂ) R⊆e.source)
    (diff : ∀ z : ℂ, r<‖z‖ → ‖z‖<R → DifferentiableAt ℝ e z)
    (cJ : ContinuousOn (fun z : ℂ => |(fderiv ℝ e z).det|) {z | r≤‖z‖ ∧ ‖z‖≤R}) :
    (∫ s in r..R, ∫ θ in (-π)..π, s*|(fderiv ℝ e (circleMap 0 s θ)).det|)≤
      planeDiskImageArea e R-planeDiskImageArea e r := by
  let S := {z : ℂ | r<‖z‖ ∧ ‖z‖<R}
  have ms : MeasurableSet S := ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet
  have sub : S⊆ball (0:ℂ) R := fun z hz => by simpa only [mem_ball,dist_zero_right] using hz.2
  have domR := ball_subset_closedBall.trans dom
  have domr := (ball_subset_ball lt.le).trans domR
  have fin := plane_disk_image_measure_finite e dom
  have eq := integral_image_eq_integral_abs_det_fderiv_smul volume ms
    (fun z hz => (diff z hz.1 hz.2).hasFDerivAt.hasFDerivWithinAt) (e.injOn.mono (sub.trans domR)) (fun _ : ℂ => (1:ℝ))
  simp only [setIntegral_const,smul_eq_mul,mul_one] at eq
  rw [← complex_annulus_integral_polar hr lt cJ,← eq]
  have dj : Disjoint (e '' S) (e '' ball (0:ℂ) r) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ ⟨w,hw,same⟩
    have wz := e.injOn (domr hw) (domR (sub hz)) same
    have less : ‖w‖<r := by simpa only [mem_ball,dist_zero_right] using hw
    exact (hz.1.trans (wz ▸ less)).false
  have ur : e '' S ∪ e '' ball (0:ℂ) r⊆e '' ball (0:ℂ) R :=
    union_subset (image_mono sub) (image_mono (ball_subset_ball lt.le))
  have h := measureReal_mono (μ := volume) ur fin
  rw [measureReal_union dj (e.isOpen_image_of_subset_source isOpen_ball domr).measurableSet
    (measure_ne_top_of_subset (image_mono sub) fin)
    (measure_ne_top_of_subset (image_mono (ball_subset_ball lt.le)) fin)] at h
  exact le_sub_iff_add_le.mpr h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_annulus_jacobian_area
