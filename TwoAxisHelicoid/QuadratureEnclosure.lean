import TwoAxisHelicoid.HorizontalCertificate

namespace TwoAxisHelicoid
open ComplexBall Metric

theorem quadrature_enclosure {K N : ℕ} {q : QuadratureRule K} (hq : q.ExactTo N)
    (hqn : q.NodesInUnit) {f : ℂ → ℂ} {c : ℂ} {h R M : ℚ}
    (hh0 : 0 ≤ h) (hhR : h < R) (hf : DiffContOnCl ℂ f (ball c (R : ℝ)))
    (hbound : ∀ z ∈ closedBall c (R : ℝ), ‖f z‖ ≤ (M : ℝ))
    {nodes : Fin K → ComplexBall} (hnodes : ∀ i, (nodes i).Contains
      ((q.weight i : ℂ)*f (c+(h : ℂ)*(q.node i : ℂ))))
    {out : ComplexBall} (hout : out.coarsens ((sumBalls nodes).inflate (quadratureErrorBound q N h R M))) :
    out.Contains (normalizedIntegral f c (h : ℝ)) := by
  have hh : (0 : ℝ) ≤ h := by exact_mod_cast hh0
  have hhR' : (h : ℝ) < R := by exact_mod_cast hhR
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg _).trans
    (hbound c (mem_closedBall_self (hh.trans hhR'.le)))
  have herr := QuadratureRule.analytic_error_bound hq hqn hh hhR' hM0 hf
    (fun z hz => hbound z (sphere_subset_closedBall hz))
  have herr' : ‖normalizedIntegral f c (h : ℝ)-q.apply f c (h : ℝ)‖ ≤
      (quadratureErrorBound q N h R M : ℝ) := by
    simpa only [quadratureErrorBound, Rat.cast_mul, Rat.cast_add, Rat.cast_one,
      Rat.cast_div, Rat.cast_pow, Rat.cast_sub] using herr
  have hsum : (sumBalls nodes).Contains (q.apply f c (h : ℝ)) := by
    simpa only [QuadratureRule.apply, Complex.ofReal_ratCast] using sumBalls_contains hnodes
  exact coarsen_contains (inflate_contains hsum herr') hout

end TwoAxisHelicoid
