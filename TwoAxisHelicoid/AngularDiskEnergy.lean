import TwoAxisHelicoid.OpenDiskBoundaryDiameter
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace TwoAxisHelicoid
open Complex Real Set Filter MeasureTheory Metric
open scoped Interval Topology

/-- Cauchy-Schwarz for an integral over a real interval, obtained by
integrating the square around its average. -/
theorem interval_integral_square_le {a b : ℝ} (ab : a<b) {f : ℝ → ℝ} (cf : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, f x)^2≤(b-a)*(∫ x in a..b, f x^2) := by
  let I := ∫ x in a..b, f x
  let m := I/(b-a)
  have fi : IntervalIntegrable f volume a b := cf.intervalIntegrable_of_Icc (μ := volume) ab.le
  have sq : IntervalIntegrable (fun x => f x^2) volume a b := (cf.pow 2).intervalIntegrable_of_Icc (μ := volume) ab.le
  have nn := intervalIntegral.integral_nonneg (μ := volume) (f := fun x => (f x-m)^2) ab.le (fun _ _ => sq_nonneg _)
  have funEq : (fun x => (f x-m)^2)=(fun x => f x^2-2*m*f x+m^2) := by funext x; ring
  have cross : IntervalIntegrable (fun x => 2*m*f x) volume a b := fi.const_mul _
  have sum : IntervalIntegrable (fun x => f x^2-2*m*f x) volume a b := sq.sub cross
  rw [funEq,intervalIntegral.integral_add sum intervalIntegrable_const,
    intervalIntegral.integral_sub sq cross,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,smul_eq_mul] at nn
  change 0≤(∫ x in a..b, f x^2)-2*m*I+(b-a)*m^2 at nn
  have hba := sub_pos.mpr ab
  have avg : m*(b-a)=I := by dsimp [m]; field_simp
  change I^2≤_
  nlinarith [mul_nonneg hba.le nn,congrArg (fun v : ℝ => v^2) avg,congrArg (fun v : ℝ => v*I) avg]

private theorem sphere_angle_interval {r : ℝ} {z : ℂ} (hz : z∈sphere (0:ℂ) r) :
    ∃ θ∈Icc (-π) π, circleMap 0 r θ=z := by
  have norm : ‖z‖=r := by simpa only [mem_sphere,dist_zero_right] using hz
  refine ⟨z.arg,⟨(Complex.neg_pi_lt_arg _).le,Complex.arg_le_pi _⟩,?_⟩
  rw [circleMap_zero,← norm,Complex.norm_mul_exp_arg_mul_I]

/-- Energy on the boundary circle controls the entire diameter of the
image of the disk, including points at its center where the derivative
of the coordinate need not exist. -/
theorem disk_dist_sq_le_angular_energy (e : OpenPartialHomeomorph ℂ ℂ) {r : ℝ}
    (hr : 0<r) (domain : closedBall (0:ℂ) r⊆e.source)
    {v : ℝ → ℂ} (cv : Continuous v)
    (drv : ∀ θ, HasDerivAt (e ∘ circleMap 0 r) (v θ) θ)
    {z w : ℂ} (hz : z∈closedBall (0:ℂ) r) (hw : w∈closedBall (0:ℂ) r) :
    dist (e z) (e w)^2≤8*π*(∫ θ in (-π)..π, ‖v θ‖^2) := by
  let a := -π
  let g := e ∘ circleMap 0 r
  let I := ∫ θ in a..π, ‖v θ‖
  have ap : a<π := by dsimp [a]; linarith [Real.pi_pos]
  have base (θ : ℝ) (hθ : θ∈Icc a π) : dist (g θ) (g a)≤I := by
    rw [dist_eq_norm,← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => drv t) (cv.intervalIntegrable a θ)]
    exact (intervalIntegral.norm_integral_le_integral_norm hθ.1).trans
      (intervalIntegral.integral_mono_interval le_rfl hθ.1 hθ.2 (.of_forall fun t => norm_nonneg (v t))
        (cv.norm.intervalIntegrable a π))
  have bd (x : ℂ) (hx : x∈sphere (0:ℂ) r) (y : ℂ) (hy : y∈sphere (0:ℂ) r) : dist (e x) (e y)≤I+I := by
    obtain ⟨s,hs,rfl⟩ := sphere_angle_interval hx
    obtain ⟨t,ht,rfl⟩ := sphere_angle_interval hy
    change dist (g s) (g t)≤I+I
    exact (dist_triangle_right _ _ (g a)).trans (add_le_add (base s hs) (base t ht))
  have limit := open_disk_diameter_le_boundary e hr domain bd hz hw
  have square := interval_integral_square_le ap cv.norm.continuousOn
  change I^2≤(π-a)*_ at square
  dsimp [a] at square
  nlinarith [sq_le_sq₀ (dist_nonneg (x := e z) (y := e w)) ((dist_nonneg (x := e z) (y := e w)).trans limit) |>.2 limit]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.disk_dist_sq_le_angular_energy
