import TwoAxisHelicoid.OrientedMinimalHarmonicAtlas
import TwoAxisHelicoid.ExteriorComplexEnd

namespace TwoAxisHelicoid
open Bornology Complex Filter Set Topology InnerProductSpace
open scoped Topology Manifold ContDiff

/-- A compatible holomorphic chart on the induced complex surface expresses
the original spatial map by a real-differentiable immersion at all its finite
points. This applies directly to the exterior chart of the geometric end. -/
theorem differentiable_in_actual_holomorphic_chart {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (X : M → Fin 3 → ℝ) (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {z : ℂ} (hz : z ∈ e.target) : DifferentiableAt ℝ (X ∘ e.symm) z := by
  let x := e.symm z
  let d := chartAt ℂ x
  have hx : x ∈ d.source := mem_chart_source ℂ x
  obtain ⟨hh,_,_⟩ := hX d (chart_mem_atlas ℂ x) _ (d.map_source hx)
  have hD : DifferentiableAt ℝ (X ∘ d.symm) (d x) :=
    (analyticAt_pi_iff.mpr fun j => _root_.HarmonicAt.analyticAt (hh j)).differentiableAt
  have htrans := (contMDiffAt_of_mem_maximalAtlas (I := 𝓘(ℂ,ℂ)) (n := ω)
    (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)) hx).comp z (contMDiffAt_symm_of_mem_maximalAtlas he hz)
  have hU : DifferentiableAt ℝ (d ∘ e.symm) z := htrans.contDiffAt.analyticAt.differentiableAt.restrictScalars ℝ
  apply (hD.comp z hU).congr_of_eventuallyEq
  filter_upwards [(e.symm.continuousAt hz).eventually (d.open_source.mem_nhds hx)] with w hw
  exact congrArg X (d.left_inv hw).symm

theorem exterior_immersion_eventually_differentiable {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M]
    (X : M → Fin 3 → ℝ) (hX : ∀ d ∈ atlas ℂ M, HarmonicImmersionChart X d)
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {R : ℝ} (ht : e.target = {ζ : ℂ | R < ‖ζ‖}) :
    ∀ᶠ z in cobounded ℂ, DifferentiableAt ℝ (X ∘ e.symm) z := by
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
  exact differentiable_in_actual_holomorphic_chart X hX he (ht ▸ hz)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.exterior_immersion_eventually_differentiable
