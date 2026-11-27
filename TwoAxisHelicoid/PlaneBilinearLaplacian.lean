import TwoAxisHelicoid.AnalyticPlaneLaplacian
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.CrossProduct

namespace TwoAxisHelicoid
open Complex Filter InnerProductSpace Laplacian Matrix
open scoped Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

theorem planePartial_bilinear (B : E →L[ℝ] F →L[ℝ] G) {f : ℂ → E} {g : ℂ → F} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (v : ℂ) :
    planePartial v (fun w => B (f w) (g w)) z =
      B (f z) (planePartial v g z) + B (planePartial v f z) (g z) :=
  congrArg (fun D : ℂ →L[ℝ] G => D v) (B.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).fderiv

theorem laplacian_bilinear_plane [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (B : E →L[ℝ] F →L[ℝ] G) {f : ℂ → E} {g : ℂ → F} {z : ℂ}
    (hf : AnalyticAt ℝ f z) (hg : AnalyticAt ℝ g z) :
    (Δ (fun w => B (f w) (g w))) z = B (f z) ((Δ g) z) + B ((Δ f) z) (g z) +
      (B (planePartial 1 f z) (planePartial 1 g z) + B (planePartial I f z) (planePartial I g z)) +
      (B (planePartial 1 f z) (planePartial 1 g z) + B (planePartial I f z) (planePartial I g z)) := by
  have hA : AnalyticAt ℝ (fun w => B (f w) (g w)) z :=
    (B.analyticAt_bilinear (f z,g z)).comp₂ hf hg
  have h (v : ℂ) : planePartial v (planePartial v (fun w => B (f w) (g w))) z =
      B (f z) (planePartial v (planePartial v g) z) + B (planePartial v (planePartial v f) z) (g z)
      + B (planePartial v f z) (planePartial v g z) + B (planePartial v f z) (planePartial v g z) := by
    let a := fun w => B (f w) (planePartial v g w)
    let b := fun w => B (planePartial v f w) (g w)
    have he : planePartial v (fun w => B (f w) (g w)) =ᶠ[𝓝 z] (fun w => a w+b w) := by
      filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with w hw hgw
      exact planePartial_bilinear B hw.differentiableAt hgw.differentiableAt v
    have hd := congrArg (fun D : ℂ →L[ℝ] G => D v) (he.fderiv_eq (𝕜 := ℝ))
    change planePartial v _ z = planePartial v _ z at hd
    have h₁ := (planePartial_analyticAt hf v).differentiableAt
    have h₂ := (planePartial_analyticAt hg v).differentiableAt
    have ha : DifferentiableAt ℝ a z := (B.hasFDerivAt_of_bilinear hf.differentiableAt.hasFDerivAt h₂.hasFDerivAt).differentiableAt
    have hb : DifferentiableAt ℝ b z := (B.hasFDerivAt_of_bilinear h₁.hasFDerivAt hg.differentiableAt.hasFDerivAt).differentiableAt
    rw [hd,planePartial_add ha hb]
    dsimp only [a,b]
    rw [planePartial_bilinear B hf.differentiableAt h₂,planePartial_bilinear B h₁ hg.differentiableAt]
    abel
  rw [laplacian_plane_partials hA,laplacian_plane_partials hg,laplacian_plane_partials hf,h,h]
  simp only [map_add,_root_.add_apply]
  abel

noncomputable def spatialDotBilinear : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ :=
  (dotProductBilin ℝ ℝ).toContinuousBilinearMap

noncomputable def spatialCrossBilinear : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  crossProduct.toContinuousBilinearMap

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.laplacian_bilinear_plane
