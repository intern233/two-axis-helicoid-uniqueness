import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Ring

namespace TwoAxisHelicoid
open Complex Filter InnerProductSpace Laplacian
open scoped Topology InnerProductSpace

noncomputable def planePartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℂ) (f : ℂ → E) (z : ℂ) : E := fderiv ℝ f z v

theorem planePartial_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} {z : ℂ} (hf : AnalyticAt ℝ f z) (v : ℂ) : AnalyticAt ℝ (planePartial v f) z :=
  ((ContinuousLinearMap.apply ℝ E v).analyticAt _).comp hf.fderiv

theorem laplacian_plane_partials {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} {z : ℂ} (hf : AnalyticAt ℝ f z) :
    (Δ f) z = planePartial 1 (planePartial 1 f) z + planePartial I (planePartial I f) z := by
  have h (v : ℂ) : planePartial v (planePartial v f) z = fderiv ℝ (fderiv ℝ f) z v v := by
    have hd := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp z hf.fderiv.differentiableAt.hasFDerivAt
    change fderiv ℝ ((ContinuousLinearMap.apply ℝ E v) ∘ fderiv ℝ f) z v = _
    rw [hd.fderiv]
    rfl
  simp only [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,h,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem planePartial_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℂ → E} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (v : ℂ) :
    planePartial v (fun w => f w+g w) z = planePartial v f z + planePartial v g z := by
  exact congrArg (fun D : ℂ →L[ℝ] E => D v) (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv

theorem planePartial_mul {f g : ℂ → ℝ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (v : ℂ) :
    planePartial v (fun w => f w*g w) z = f z*planePartial v g z + g z*planePartial v f z := by
  exact congrArg (fun D : ℂ →L[ℝ] ℝ => D v) (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv

theorem laplacian_mul_plane {f g : ℂ → ℝ} {z : ℂ} (hf : AnalyticAt ℝ f z) (hg : AnalyticAt ℝ g z) :
    (Δ (fun w => f w*g w)) z = f z*(Δ g) z + g z*(Δ f) z +
      2*(planePartial 1 f z*planePartial 1 g z + planePartial I f z*planePartial I g z) := by
  have h (v : ℂ) : planePartial v (planePartial v (fun w => f w*g w)) z =
      f z*planePartial v (planePartial v g) z + g z*planePartial v (planePartial v f) z +
        2*planePartial v f z*planePartial v g z := by
    have he : planePartial v (fun w => f w*g w) =ᶠ[𝓝 z]
        (fun w => f w*planePartial v g w + g w*planePartial v f w) := by
      filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with w hw hgw
      exact planePartial_mul hw.differentiableAt hgw.differentiableAt v
    have hd := congrArg (fun D : ℂ →L[ℝ] ℝ => D v) (he.fderiv_eq (𝕜 := ℝ))
    have h₁ := (planePartial_analyticAt hf v).differentiableAt
    have h₂ := (planePartial_analyticAt hg v).differentiableAt
    change planePartial v _ z = planePartial v _ z at hd
    rw [hd,planePartial_add (f := fun w => f w*planePartial v g w) (g := fun w => g w*planePartial v f w) (hf.differentiableAt.mul h₂) (hg.differentiableAt.mul h₁),
      planePartial_mul hf.differentiableAt h₂,planePartial_mul hg.differentiableAt h₁]
    ring
  rw [laplacian_plane_partials (f := fun w => f w*g w) (hf.mul hg),laplacian_plane_partials hg,laplacian_plane_partials hf,h,h]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.laplacian_mul_plane
