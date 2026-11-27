import TwoAxisHelicoid.HarmonicTangentLaplacian
import TwoAxisHelicoid.MinimalGraphClosedForm
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace TwoAxisHelicoid
open Complex Filter Topology InnerProductSpace Laplacian
open scoped Topology ContDiff

/-- The trace of the real second-derivative chain rule on the complex
parameter plane. Both domain and target coordinates of the inner map
are ordinary real two-dimensional coordinates. -/
theorem analytic_plane_laplacian_comp {U : ℂ → ℂ} {g : ℂ → ℝ} {z : ℂ}
    (hU : AnalyticAt ℝ U z) (hg : AnalyticAt ℝ g (U z)) :
    let D := fderiv ℝ (fderiv ℝ g) (U z)
    (Δ (g ∘ U)) z = fderiv ℝ g (U z) ((Δ U) z) +
      D (planePartial 1 U z) (planePartial 1 U z) + D (planePartial I U z) (planePartial I U z) := by
  let D := fderiv ℝ (fderiv ℝ g) (U z)
  have second (v : ℂ) :
      planePartial v (planePartial v (g ∘ U)) z =
      fderiv ℝ g (U z) (planePartial v (planePartial v U) z)+D (planePartial v U z) (planePartial v U z) := by
    have germ : planePartial v (g ∘ U) =ᶠ[𝓝 z] fun w => fderiv ℝ g (U w) (planePartial v U w) := by
      filter_upwards [hU.eventually_analyticAt,hU.continuousAt hg.eventually_analyticAt] with w hu ha
      exact congrArg (fun F : ℂ →L[ℝ] ℝ => F v) (ha.differentiableAt.hasFDerivAt.comp w hu.differentiableAt.hasFDerivAt).fderiv
    have d := ((hg.fderiv.differentiableAt.hasFDerivAt.comp z hU.differentiableAt.hasFDerivAt).clm_apply
      (planePartial_analyticAt hU v).differentiableAt.hasFDerivAt).fderiv
    exact congrArg (fun F : ℂ →L[ℝ] ℝ => F v) ((germ.fderiv_eq (𝕜 := ℝ)).trans d)
  change (Δ (g ∘ U)) z = _+D _ _+D _ _
  rw [laplacian_plane_partials (hg.comp hU),laplacian_plane_partials hU,second 1,second I,map_add]
  ring

/-- The coefficients of the Hessian in the real and imaginary directions
give an explicit formula for its trace on a pair of vectors. -/
theorem analytic_plane_hessian_trace {g : ℂ → ℝ} {w : ℂ} (hg : AnalyticAt ℝ g w) (v u : ℂ) :
    let D := fderiv ℝ (fderiv ℝ g) w
    D v v+D u u = D 1 1*(v.re^2+u.re^2)+2*D 1 I*(v.re*v.im+u.re*u.im)+D I I*(v.im^2+u.im^2) := by
  let D := fderiv ℝ (fderiv ℝ g) w
  have sym : D I 1=D 1 I := hg.contDiffAt.isSymmSndFDerivAt_of_omega I 1
  have eval (t : ℂ) :
      D t t = D 1 1*t.re^2+2*D 1 I*t.re*t.im+D I I*t.im^2 := by
    rw [real_linear_complex_expansion D t]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [real_linear_complex_expansion (D 1) t,real_linear_complex_expansion (D I) t]
    simp only [smul_eq_mul,sym]
    ring
  change D v v+D u u=_
  rw [eval v,eval u]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_plane_laplacian_comp
#print axioms TwoAxisHelicoid.analytic_plane_hessian_trace
