import TwoAxisHelicoid.PlaneBilinearLaplacian
import TwoAxisHelicoid.HarmonicTangentLaplacian

namespace TwoAxisHelicoid
open Complex Matrix Filter Laplacian InnerProductSpace
open scoped Topology

theorem spatialDotBilinear_eq (u v : Fin 3 → ℝ) : spatialDotBilinear u v = u ⬝ᵥ v := rfl

theorem planePartial_dot {X Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z) (v : ℂ) :
    planePartial v (fun w => X w ⬝ᵥ Y w) z =
      X z ⬝ᵥ planePartial v Y z + planePartial v X z ⬝ᵥ Y z :=
  planePartial_bilinear spatialDotBilinear hX hY v

theorem spatial_laplacian_dot {X Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : AnalyticAt ℝ X z) (hY : AnalyticAt ℝ Y z) :
    (Δ (fun w => X w ⬝ᵥ Y w)) z = X z ⬝ᵥ (Δ Y) z + (Δ X) z ⬝ᵥ Y z +
      2*(planePartial 1 X z ⬝ᵥ planePartial 1 Y z + planePartial I X z ⬝ᵥ planePartial I Y z) := by
  simpa only [spatialDotBilinear_eq,two_mul,add_assoc] using laplacian_bilinear_plane spatialDotBilinear hX hY

theorem derivative_of_constant_pairing {X Y : ℂ → Fin 3 → ℝ} {z : ℂ} {c : ℝ}
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z)
    (he : (fun w => X w ⬝ᵥ Y w) =ᶠ[𝓝 z] (fun _ => c)) (v : ℂ) :
    X z ⬝ᵥ planePartial v Y z + planePartial v X z ⬝ᵥ Y z = 0 := by
  rw [← planePartial_dot hX hY v]
  change fderiv ℝ _ z v = 0
  rw [he.fderiv_eq,(hasFDerivAt_const c z).fderiv]
  rfl

theorem derivative_of_equal_squared_norms {X Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z)
    (he : (fun w => X w ⬝ᵥ X w) =ᶠ[𝓝 z] (fun w => Y w ⬝ᵥ Y w)) (v : ℂ) :
    planePartial v X z ⬝ᵥ X z = planePartial v Y z ⬝ᵥ Y z := by
  have h := congrArg (fun D : ℂ →L[ℝ] ℝ => D v) (he.fderiv_eq (𝕜 := ℝ))
  change planePartial v _ z = planePartial v _ z at h
  rw [planePartial_dot hX hX,planePartial_dot hY hY,dotProduct_comm (X z) _,dotProduct_comm (Y z) _] at h
  linarith

theorem laplacian_of_constant_pairing {X Y : ℂ → Fin 3 → ℝ} {z : ℂ} {c : ℝ}
    (hX : AnalyticAt ℝ X z) (hY : AnalyticAt ℝ Y z)
    (he : (fun w => X w ⬝ᵥ Y w) =ᶠ[𝓝 z] (fun _ => c)) :
    X z ⬝ᵥ (Δ Y) z + (Δ X) z ⬝ᵥ Y z +
      2*(planePartial 1 X z ⬝ᵥ planePartial 1 Y z + planePartial I X z ⬝ᵥ planePartial I Y z) = 0 := by
  rw [← spatial_laplacian_dot hX hY,(laplacian_congr_nhds he).self_of_nhds]
  simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.laplacian_of_constant_pairing
