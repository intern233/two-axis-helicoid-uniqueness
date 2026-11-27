import TwoAxisHelicoid.AngularDiskEnergy
import TwoAxisHelicoid.DistortionImageArea
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace TwoAxisHelicoid
open Complex Real Set Metric Filter MeasureTheory
open scoped Interval Topology

private theorem continuous_radius_circle : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  simp only [circleMap_zero]
  fun_prop

theorem continuousOn_radial_jacobian_integral {r R : ℝ} (hr : 0<r) {J : ℂ → ℝ}
    (c : ContinuousOn J {z | r≤‖z‖ ∧ ‖z‖≤R}) :
    ContinuousOn (fun s : ℝ => ∫ θ in (-π)..π, s*J (circleMap 0 s θ)) (Icc r R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  let p := fun x : Icc r R × ℝ => circleMap 0 x.1.1 x.2
  have cp : Continuous p := continuous_radius_circle.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have cJ : Continuous (J ∘ p) := continuous_iff_continuousAt.mpr fun x =>
    Filter.Tendsto.comp (c (p x) (by
      change r≤‖circleMap 0 x.1.1 x.2‖ ∧ ‖circleMap 0 x.1.1 x.2‖≤R
      rw [norm_circleMap_zero,abs_of_nonneg (hr.le.trans x.1.2.1)]
      exact x.1.2)) (tendsto_nhdsWithin_iff.mpr ⟨cp.continuousAt.tendsto,.of_forall fun y => by
        change r≤‖circleMap 0 y.1.1 y.2‖ ∧ ‖circleMap 0 y.1.1 y.2‖≤R
        rw [norm_circleMap_zero,abs_of_nonneg (hr.le.trans y.1.2.1)]
        exact y.1.2⟩)
  change Continuous (fun x : Icc r R × ℝ => x.1.1*J (p x))
  exact (continuous_subtype_val.comp continuous_fst).mul cJ

/-- The true radial Jacobian integral bounds any squared distance
inside the disk. The singularity at its center is harmless. -/
theorem distorted_circle_disk_bound (e : OpenPartialHomeomorph ℂ ℂ) {s K : ℝ}
    (hs : 0<s) (dom : closedBall (0:ℂ) s⊆e.source)
    (diff : ∀ p∈sphere (0:ℂ) s, DifferentiableAt ℝ e p)
    (cD : ContinuousOn (fderiv ℝ (e : ℂ → ℂ)) (sphere (0:ℂ) s))
    (distort : ∀ p∈sphere (0:ℂ) s, ∀ v : ℂ, ‖fderiv ℝ e p v‖^2≤K*|(fderiv ℝ e p).det| *‖v‖^2)
    {z w : ℂ} (hz : z∈closedBall (0:ℂ) s) (hw : w∈closedBall (0:ℂ) s) :
    dist (e z) (e w)^2≤8*π*K*s*(∫ θ in (-π)..π, s*|(fderiv ℝ e (circleMap 0 s θ)).det|) := by
  let c := circleMap (0:ℂ) s
  let v := fun θ => fderiv ℝ e (c θ) (c θ*I)
  have cs (θ : ℝ) : c θ∈sphere (0:ℂ) s := circleMap_mem_sphere 0 hs.le θ
  have cd : Continuous (fun θ => fderiv ℝ e (c θ)) := continuous_iff_continuousAt.mpr fun θ =>
    Filter.Tendsto.comp (cD _ (cs θ)) (tendsto_nhdsWithin_iff.mpr ⟨(continuous_circleMap 0 s).continuousAt.tendsto,.of_forall cs⟩)
  have cv : Continuous v := cd.clm_apply ((continuous_circleMap 0 s).mul continuous_const)
  have d (θ : ℝ) : HasDerivAt (e ∘ c) (v θ) θ :=
    (diff _ (cs θ)).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_circleMap 0 s θ)
  have h := disk_dist_sq_le_angular_energy e hs dom cv d hz hw
  let j := fun θ => |(fderiv ℝ e (c θ)).det|
  have cj : Continuous j := (ContinuousLinearMap.continuous_det.comp cd).abs
  have hpi : -π≤π := by linarith [Real.pi_pos]
  have upper := intervalIntegral.integral_mono_on (μ := volume) hpi ((cv.norm.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul (continuous_const.mul cj)).intervalIntegrable _ _) (fun θ _ => by
      have b := distort (c θ) (cs θ) (c θ*I)
      have nc : ‖c θ*I‖=s := by rw [norm_mul,Complex.norm_I,mul_one,norm_circleMap_zero,abs_of_pos hs]
      rw [nc] at b
      exact b.trans_eq (by ring : K*|(fderiv ℝ e (c θ)).det| *s^2=(K*s)*(s*j θ)))
  change (∫ θ in (-π)..π, ‖v θ‖^2)≤∫ θ in (-π)..π, (K*s)*(s*j θ) at upper
  rw [intervalIntegral.integral_const_mul] at upper
  calc
    _ ≤ 8*π*(∫ θ in (-π)..π, ‖v θ‖^2) := h
    _ ≤ 8*π*((K*s)*(∫ θ in (-π)..π, s*j θ)) := mul_le_mul_of_nonneg_left upper (by positivity)
    _ = _ := by dsimp [j,c]; ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.distorted_circle_disk_bound
