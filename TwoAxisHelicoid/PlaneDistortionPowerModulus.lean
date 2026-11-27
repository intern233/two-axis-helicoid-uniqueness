import TwoAxisHelicoid.DistortedCircleEstimate
import TwoAxisHelicoid.DyadicDiskDistortion

namespace TwoAxisHelicoid
open Complex Real Set Metric MeasureTheory Filter
open scoped Interval Topology

theorem distorted_half_disk_distance (e : OpenPartialHomeomorph ℂ ℂ) {R K : ℝ}
    (hR : 0<R) (hK : 0≤K) (dom : closedBall (0:ℂ) R⊆e.source)
    (diff : ∀ z : ℂ, 0<‖z‖ → ‖z‖≤R → ContDiffAt ℝ 1 e z)
    (distort : ∀ z : ℂ, 0<‖z‖ → ‖z‖≤R → ∀ v : ℂ,
      ‖fderiv ℝ e z v‖^2≤K*|(fderiv ℝ e z).det| *‖v‖^2)
    {z w : ℂ} (hz : z∈closedBall (0:ℂ) (R/2)) (hw : w∈closedBall (0:ℂ) (R/2)) :
    dist (e z) (e w)^2≤16*π*K*(planeDiskImageArea e R-planeDiskImageArea e (R/2)) := by
  let r := R/2
  have hr : 0<r := half_pos hR
  have lt : r<R := half_lt_self hR
  let J := fun p : ℂ => |(fderiv ℝ e p).det|
  let F := fun s : ℝ => ∫ θ in (-π)..π, s*J (circleMap 0 s θ)
  have cD (p : ℂ) (hp : r≤‖p‖ ∧ ‖p‖≤R) : ContinuousAt (fderiv ℝ (e : ℂ → ℂ)) p :=
    (diff p (hr.trans_le hp.1) hp.2).continuousAt_fderiv one_ne_zero
  have cJ : ContinuousOn J {p : ℂ | r≤‖p‖ ∧ ‖p‖≤R} := fun p hp =>
    (ContinuousLinearMap.continuous_det.continuousAt.comp (cD p hp)).abs.continuousWithinAt
  have fi := (continuousOn_radial_jacobian_integral hr cJ).intervalIntegrable_of_Icc (μ := volume) lt.le
  have hπ : -π≤π := by linarith [Real.pi_pos]
  have nn (s : ℝ) (hs : s∈Icc r R) : 0≤F s :=
    intervalIntegral.integral_nonneg hπ (fun θ _ => mul_nonneg (hr.le.trans hs.1) (abs_nonneg _))
  have point (s : ℝ) (hs : s∈Icc r R) : dist (e z) (e w)^2≤(8*π*K*R)*F s := by
    have sp := hr.trans_le hs.1
    have cp (p : ℂ) (hp : p∈sphere (0:ℂ) s) : r≤‖p‖ ∧ ‖p‖≤R := by
      have n : ‖p‖=s := by simpa only [mem_sphere,dist_zero_right] using hp
      rwa [n]
    have h := distorted_circle_disk_bound e sp ((closedBall_subset_closedBall hs.2).trans dom)
      (fun p hp => (diff p (hr.trans_le (cp p hp).1) (cp p hp).2).differentiableAt one_ne_zero)
      (fun p hp => (cD p (cp p hp)).continuousWithinAt)
      (fun p hp => distort p (hr.trans_le (cp p hp).1) (cp p hp).2)
      (closedBall_subset_closedBall hs.1 hz) (closedBall_subset_closedBall hs.1 hw)
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs.2 (by positivity)) (nn s hs))
  have outer := intervalIntegral.integral_mono_on lt.le intervalIntegrable_const (fi.const_mul (8*π*K*R)) point
  rw [intervalIntegral.integral_const,smul_eq_mul,intervalIntegral.integral_const_mul] at outer
  have ar := plane_annulus_jacobian_area e hr lt dom
    (fun p h1 h2 => (diff p (hr.trans h1) h2.le).differentiableAt one_ne_zero) cJ
  change (∫ s in r..R,F s)≤_ at ar
  have mul := outer.trans (mul_le_mul_of_nonneg_left ar (by positivity))
  apply le_of_mul_le_mul_left (a := R/2) _ hr
  change (R/2)*_≤_
  convert mul using 1 <;> dsimp [r] <;> ring

/-- A punctured C¹ plane coordinate of bounded distortion has a
power modulus at its center, with an actual natural exponent. -/
theorem plane_coordinate_power_modulus (e : OpenPartialHomeomorph ℂ ℂ) {R K : ℝ}
    (hR : 0<R) (hK : 0<K) (dom : closedBall (0:ℂ) R⊆e.source)
    (diff : ∀ z : ℂ, 0<‖z‖ → ‖z‖≤R → ContDiffAt ℝ 1 e z)
    (distort : ∀ z : ℂ, 0<‖z‖ → ‖z‖≤R → ∀ v : ℂ,
      ‖fderiv ℝ e z v‖^2≤K*|(fderiv ℝ e z).det| *‖v‖^2) :
    ∃ N : ℕ, 0<N ∧ ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, 0<‖z‖ → ‖z‖≤R/2 → ‖e z-e 0‖^N≤C*‖z‖ := by
  let A := planeDiskImageArea e
  let B := 16*π*K
  let L := π*B
  let q := L/(1+L)
  have b : 0<B := by dsimp [B]; positivity
  have l : 0<L := mul_pos Real.pi_pos b
  have p : 0<1+L := by positivity
  have aq (r : ℝ) : 0≤A r := ENNReal.toReal_nonneg
  have distb (r : ℝ) (hr : 0<r) (small : r≤R) (z : ℂ) (hz : ‖z‖≤r/2) :
      dist (e z) (e 0)^2≤B*(A r-A (r/2)) := by
    exact distorted_half_disk_distance e hr hK.le ((closedBall_subset_closedBall small).trans dom)
      (fun w hw h => diff w hw (h.trans small)) (fun w hw h => distort w hw (h.trans small))
      (by simpa only [mem_closedBall,dist_zero_right] using hz) (mem_closedBall_self (half_pos hr).le)
  apply dyadic_disk_power_modulus A _ hR (div_nonneg l.le p.le) ((div_lt_one p).mpr (by linarith)) b.le (aq R)
  · intro r hr small
    have ar := plane_disk_area_le_dist_bound e (half_pos hr) (fun z hz => distb r hr small z
      (by have hn : ‖z‖<r/2 := by simpa only [mem_ball,dist_zero_right] using hz
          exact hn.le))
    change A (r/2)≤π*(B*(A r-A (r/2))) at ar
    change A (r/2)≤(L/(1+L))*A r
    rw [div_mul_eq_mul_div,le_div_iff₀ p]
    dsimp [L]
    nlinarith
  · intro r hr small z hz
    rw [← dist_eq_norm]
    exact (distb r hr small z hz).trans (mul_le_mul_of_nonneg_left (sub_le_self _ (aq _)) b.le)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_coordinate_power_modulus
