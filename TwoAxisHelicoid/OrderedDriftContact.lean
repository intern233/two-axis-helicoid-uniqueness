import TwoAxisHelicoid.PlanarDriftStrongMinimum

namespace TwoAxisHelicoid
open Complex Filter Set Topology InnerProductSpace Laplacian
open scoped Topology

private theorem nonnegative_drift_solution_zero {f A B : ℂ → ℝ} {x : ℂ}
    (hf : AnalyticAt ℝ f x) (hA : ContinuousAt A x) (hB : ContinuousAt B x) (hx : f x=0)
    (nn : ∀ᶠ z in 𝓝 x, 0 ≤ f z)
    (eq : ∀ᶠ z in 𝓝 x, (Δ f) z = A z*planePartial 1 f z+B z*planePartial I f z) :
    f =ᶠ[𝓝 x] fun _ => 0 := by
  let K := max |A x| |B x|+1
  have ak : |A x|<K := by dsimp [K]; linarith [le_max_left |A x| |B x|]
  have bk : |B x|<K := by dsimp [K]; linarith [le_max_right |A x| |B x|]
  have hk := (abs_nonneg (A x)).trans ak.le
  apply analytic_planar_strong_minimum hk hx hf.eventually_analyticAt nn
  filter_upwards [hA.abs.eventually_lt continuousAt_const ak,hB.abs.eventually_lt continuousAt_const bk,eq,nn] with z ha hb he hn
  rw [he]
  calc A z*planePartial 1 f z+B z*planePartial I f z
      ≤ |A z*planePartial 1 f z|+|B z*planePartial I f z| := add_le_add (le_abs_self _) (le_abs_self _)
    _ = |A z| * |planePartial 1 f z|+|B z| * |planePartial I f z| := by rw [abs_mul,abs_mul]
    _ ≤ K * |planePartial 1 f z|+K * |planePartial I f z| :=
      add_le_add (mul_le_mul_of_nonneg_right ha.le (abs_nonneg _)) (mul_le_mul_of_nonneg_right hb.le (abs_nonneg _))
    _ ≤ K*(|planePartial 1 f z|+|planePartial I f z|+f z) := by nlinarith [mul_nonneg hk hn]

/-- A solution of a scalar equation with continuous drift in a conformal
parameter plane has no one-sided zero except when its germ vanishes. -/
theorem planar_drift_one_sided_contact {f A B : ℂ → ℝ} {x : ℂ}
    (hf : AnalyticAt ℝ f x) (hA : ContinuousAt A x) (hB : ContinuousAt B x) (hx : f x=0)
    (side : (∀ᶠ z in 𝓝 x, 0 ≤ f z) ∨ (∀ᶠ z in 𝓝 x, f z ≤ 0))
    (eq : ∀ᶠ z in 𝓝 x, (Δ f) z = A z*planePartial 1 f z+B z*planePartial I f z) :
    f =ᶠ[𝓝 x] fun _ => 0 := by
  rcases side with nn | np
  · exact nonnegative_drift_solution_zero hf hA hB hx nn eq
  have n : ∀ᶠ z in 𝓝 x, 0 ≤ (-f) z := np.mono (fun _ h => neg_nonneg.mpr h)
  have sol : ∀ᶠ z in 𝓝 x, (Δ (-f)) z=A z*planePartial 1 (-f) z+B z*planePartial I (-f) z := by
    filter_upwards [eq,hf.eventually_analyticAt] with z he ha
    rw [laplacian_neg,Pi.neg_apply,he]
    have negd (v : ℂ) : planePartial v (-f) z = -planePartial v f z :=
      congrArg (fun D : ℂ →L[ℝ] ℝ => D v) ha.differentiableAt.hasFDerivAt.neg.fderiv
    rw [negd,negd]
    ring
  have done := nonnegative_drift_solution_zero (f := -f) hf.neg hA hB (by simp [hx]) n sol
  exact done.mono fun _ hz => neg_eq_zero.mp hz

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.planar_drift_one_sided_contact
