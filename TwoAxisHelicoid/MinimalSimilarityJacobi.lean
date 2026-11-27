import TwoAxisHelicoid.HarmonicGaussNormalEquation
import TwoAxisHelicoid.ImmersedSimilarityRigidity
import TwoAxisHelicoid.SimilaritySymmetry

namespace TwoAxisHelicoid
open Complex Matrix Filter InnerProductSpace Laplacian
open scoped Topology ContDiff

/-- In a conformal chart of metric g(dx²+dy²), this is Δ_surface u plus
the Hilbert--Schmidt norm squared of dN times u. -/
noncomputable def conformalSurfaceJacobi (X : ℂ → Fin 3 → ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  let A := planePartial 1 X z
  let nx := planePartial 1 (harmonicChartNormal X) z
  let ny := planePartial I (harmonicChartNormal X) z
  ((Δ u) z + (nx ⬝ᵥ nx + ny ⬝ᵥ ny)*u z)/(A ⬝ᵥ A)

/-- Every infinitesimal Euclidean similarity has a Jacobi normal component
on any regular harmonic conformal chart. -/
theorem similarity_normal_solves_jacobi {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hreg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧
      ConformalCoordinateDerivatives X w ∧ Function.Injective (fderiv ℝ X w))
    (a b : Fin 3 → ℝ) (d : ℝ) :
    conformalSurfaceJacobi X (similarityNormal X (harmonicChartNormal X) a b d) z = 0 := by
  let N := harmonicChartNormal X
  let A := planePartial 1 X z
  let B := planePartial I X z
  let nx := planePartial 1 N z
  let ny := planePartial I N z
  let V := nx ⬝ᵥ nx + ny ⬝ᵥ ny
  let P := similarityLinear b d
  let W := fun w => a+P (X w)
  have hX : AnalyticAt ℝ X z := analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hreg.self_of_nhds.1 j)
  have hN : AnalyticAt ℝ N z := (harmonicChartNormal_data hX hreg.self_of_nhds.2.1 hreg.self_of_nhds.2.2).1
  have hW : AnalyticAt ℝ W z := analyticAt_const.add ((P.analyticAt _).comp hX)
  have hd (v : ℂ) : planePartial v W z = P (planePartial v X z) := by
    have h := (P.hasFDerivAt.comp z hX.differentiableAt.hasFDerivAt).const_add a
    exact congrArg (fun D : ℂ →L[ℝ] (Fin 3 → ℝ) => D v) h.fderiv
  have hL : (Δ W) z = 0 := by
    have hx2 : ContDiffAt ℝ 2 X z := hX.contDiffAt
    have hP : ContDiffAt ℝ 2 (P ∘ X) z := P.contDiff.contDiffAt.comp z hx2
    have h := (contDiffAt_const (c := a) : ContDiffAt ℝ 2 (fun _ : ℂ => a) z).laplacian_add hP
    change (Δ ((fun _ : ℂ => a)+(P ∘ X))) z = _
    simpa only [laplacian_const,Pi.zero_apply,hx2.laplacian_CLM_comp_left,Function.comp_apply,
      harmonic_coordinate_laplacian_zero hreg.self_of_nhds.1,map_zero,zero_add] using h
  have hgn : (Δ N) z = -(V • N z) := eq_neg_of_add_eq_zero_left (harmonic_chart_gauss_normal_equation hreg)
  have H := harmonic_chart_weingarten_frame hreg
  have tr : A ⬝ᵥ nx + B ⬝ᵥ ny = 0 := by
    rw [dotProduct_comm A nx,dotProduct_comm B ny,H.nxa,H.nyb,neg_add_cancel]
  have rot (T U : Fin 3 → ℝ) : (b ⨯₃ T) ⬝ᵥ U = b ⬝ᵥ (T ⨯₃ U) :=
    (dotProduct_comm _ _).trans (triple_product_permutation U b T)
  have cancel : P A ⬝ᵥ nx + P B ⬝ᵥ ny = 0 := by
    have cr := congrArg (fun U => b ⬝ᵥ U) H.normal_cross_sum
    change b ⬝ᵥ (A ⨯₃ nx + B ⨯₃ ny) = b ⬝ᵥ 0 at cr
    rw [dotProduct_add,dotProduct_zero] at cr
    simp only [P,similarityLinear_apply,add_dotProduct,smul_dotProduct,smul_eq_mul,rot]
    linear_combination cr + d*tr
  have eqn := spatial_laplacian_dot hW hN
  rw [hd,hd,hL,zero_dotProduct,add_zero,hgn,dotProduct_neg,dotProduct_smul] at eqn
  change (Δ (fun w => W w ⬝ᵥ N w)) z = -(V * (W z ⬝ᵥ N z))+2*(P A ⬝ᵥ nx + P B ⬝ᵥ ny) at eqn
  rw [cancel,mul_zero,add_zero] at eqn
  have he : similarityNormal X N a b d = fun w => W w ⬝ᵥ N w := by
    funext w
    change (a+b ⨯₃ X w+d • X w) ⬝ᵥ N w = (a+(b ⨯₃ X w+d • X w)) ⬝ᵥ N w
    rw [add_assoc]
  unfold conformalSurfaceJacobi
  change ((Δ (similarityNormal X N a b d)) z + V*(similarityNormal X N a b d z)) / (A ⬝ᵥ A) = 0
  rw [he,eqn]
  simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.similarity_normal_solves_jacobi
