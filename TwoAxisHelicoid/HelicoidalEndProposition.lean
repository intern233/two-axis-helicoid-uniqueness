import TwoAxisHelicoid.ClosedExteriorHelicoidGeometry
import TwoAxisHelicoid.ExteriorBoundaryFlux
import TwoAxisHelicoid.ZeroFluxHelicoidTube

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

/-- Proposition 2.3 on its original closed exterior. The sole extra
condition in the last clause is the three-dimensional physical flux on
the original boundary circle, computed from the actual immersion. -/
theorem proposition_2_3_helicoidal_end {X : ℂ → Fin 3 → ℝ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hfinite : ∀ z : ℂ, r ≤ ‖z‖ → AnalyticAt ℂ (infinityCorrection f) z)
    (hd : ∀ z : ℂ, r ≤ ‖z‖ → HasFDerivAt X (nullRealDerivative
      (weierstrassTriple (exp (I*z+infinityCorrection f z)) 1)) z) :
    IsProperMap (fun z : {w : ℂ // r ≤ ‖w‖} => X z.1) ∧
    (∃ C > (0:ℝ), ∀ z : ℂ, r ≤ ‖z‖ → |logGaussGaussianCurvature (fun w => I*w+infinityCorrection f w) z| ≤ C) ∧
    (∃ S : ℝ, r < S ∧ IsClosedEmbedding (fun z : {w : ℂ // S ≤ ‖w‖} => X z.1)) ∧
    ((∀ j, (closedExteriorFluxBoundary r hr).spatialConormalFlux X j = 0) →
      ∃ b : Fin 3 → ℝ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ z : ℂ, T < ‖z‖ →
        coordinateToTube (verticalRotation I (X z-b)) ∈ helicoidTubeEquiv.target ∧
        |helicoidSignedDistance (coordinateToTube (verticalRotation I (X z-b)))| ≤ ε) := by
  obtain ⟨hp,hc,he⟩ := analytic_helicoidal_end_global_geometry hf hf0 hfinite hd
  refine ⟨hp,hc,he,?_⟩
  intro flux
  let W := fun z : ℂ => I*z+infinityCorrection f z
  let p := fun z : ℂ => weierstrassTriple (exp (W z)) 1
  have hol (z : ℂ) (hz : r ≤ ‖z‖) (j : Fin 3) : DifferentiableAt ℂ (fun w => p w j) z := by
    have h : DifferentiableAt ℂ (fun w => exp (W w)) z := differentiableAt_exp.comp z
      ((differentiableAt_id.const_mul I).add (hfinite z hz).differentiableAt)
    have hn : exp (W z) ≠ 0 := exp_ne_zero _
    fin_cases j <;> dsimp [p,weierstrassTriple] <;> fun_prop
  have inner : r < r+1 := by linarith
  apply zero_flux_helicoidal_end_arbitrarily_thin hr inner (infinityCorrection_tendsto_zero hf hf0)
    (fun z hz => (hfinite z hz.le).differentiableAt) (fun z hz => hd z hz.le)
  intro j
  exact (spatial_flux_on_radius_eq_boundary hr inner X p hd (fun z _ => exponential_height_triple_null (W z))
    (fun j z hz => (hol z hz j).continuousAt.continuousWithinAt) (fun z hz j => hol z hz.le j) j).trans (flux j)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.proposition_2_3_helicoidal_end
