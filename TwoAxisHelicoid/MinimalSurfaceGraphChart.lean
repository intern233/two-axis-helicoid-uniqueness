import TwoAxisHelicoid.RegularGraphCoordinates
import TwoAxisHelicoid.MinimalSurfaceReparametrization

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology ContDiff
set_option maxHeartbeats 1300000

theorem coordinateMeanCurvature_congr {X Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (he : X =ᶠ[𝓝 z] Y) : coordinateMeanCurvature X z = coordinateMeanCurvature Y z := by
  unfold coordinateMeanCurvature
  rw [he.fderiv_eq,(he.iteratedFDeriv (𝕜 := ℝ) 2).self_of_nhds]

/-- In the regular projection chart of an arbitrary minimal parametrization,
the graph height solves the minimal-surface equation throughout an open ball. -/
theorem regular_minimal_surface_graph_chart {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (hX : ContDiffAt ℝ 2 X z) (hi : Function.Injective (fderiv ℝ X z))
    (hm : ∀ᶠ w in 𝓝 z, coordinateMeanCurvature X w = 0) :
    ∃ (σ : Equiv.Perm (Fin 3)) (e : OpenPartialHomeomorph ℂ ℂ) (u : ℂ → ℝ)
      (r : ℝ), 0 < r ∧ z ∈ e.source ∧ ContDiffAt ℝ 2 e z ∧
      ContDiffAt ℝ 2 e.symm (e z) ∧
      (∀ w ∈ e.target, (spatialPermutation σ ∘ X ∘ e.symm) w = euclideanGraph u w) ∧
      (∀ w ∈ Metric.ball (e z) r, w ∈ e.target ∧ ContDiffAt ℝ 2 u w ∧ MinimalGraphEquation u w) := by
  obtain ⟨σ,e,u,hz,he,hes,hu,hgraph⟩ := regular_immersion_graph_chart hX hi
  have hcoord (w : ℂ) (hw : w ∈ e.target) :
      (spatialPermutation σ ∘ X ∘ e.symm) w = euclideanGraph u w := by
    have h := hgraph w hw
    have ha := (Prod.mk.inj h).1
    obtain ⟨hb,hc⟩ := Prod.mk.inj (Prod.mk.inj h).2
    ext j
    fin_cases j
    · exact ha
    · exact hb
    · exact hc
  have hlim : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := e.tendsto_symm hz
  have hh : ∀ᶠ w in 𝓝 (e z), w ∈ e.target ∧ ContDiffAt ℝ 2 u w ∧ MinimalGraphEquation u w := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hz),hu.eventually (by norm_num),
      hes.eventually (by norm_num),hlim.eventually (hX.eventually (by norm_num)),hlim.eventually hm]
      with w hw huw hsw hxw hmw
    have hw' : (spatialPermutation σ ∘ X ∘ e.symm) =ᶠ[𝓝 w] euclideanGraph u := by
      filter_upwards [e.open_target.mem_nhds hw] with v hv
      exact hcoord v hv
    refine ⟨hw,huw,(euclideanGraph_zero_mean_curvature_iff huw).mp ?_⟩
    rw [← coordinateMeanCurvature_congr hw']
    exact minimal_surface_spatialPermutation (hxw.comp _ hsw) σ (minimal_surface_reparametrization hxw hsw hmw)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hh
  exact ⟨σ,e,u,r,hr,hz,he,hes,hcoord,fun _ hw => hball hw⟩

theorem graph_projection_chart_metric {X : ℂ → Fin 3 → ℝ}
    (σ : Equiv.Perm (Fin 3)) (e : OpenPartialHomeomorph ℂ ℂ) {u : ℂ → ℝ}
    (hgraph : ∀ w ∈ e.target, (spatialPermutation σ ∘ X ∘ e.symm) w = euclideanGraph u w)
    {w : ℂ} (hw : w ∈ e.target) (hu : DifferentiableAt ℝ u w)
    (hX : DifferentiableAt ℝ (X ∘ e.symm) w) (v : ℂ) :
    fderiv ℝ (X ∘ e.symm) w v ⬝ᵥ fderiv ℝ (X ∘ e.symm) w v =
      v.re^2+v.im^2+(fderiv ℝ u w v)^2 := by
  have he : (spatialPermutation σ ∘ X ∘ e.symm) =ᶠ[𝓝 w] euclideanGraph u := by
    filter_upwards [e.open_target.mem_nhds hw] with v hv
    exact hgraph v hv
  have hd := congrArg (fun D : ℂ →L[ℝ] (Fin 3 → ℝ) => D v) (he.fderiv_eq (𝕜 := ℝ))
  rw [fderiv_comp w (spatialPermutation σ).differentiableAt hX,(spatialPermutation σ).fderiv] at hd
  change spatialPermutation σ (fderiv ℝ (X ∘ e.symm) w v) = _ at hd
  rw [← spatialPermutation_dot σ,hd,euclideanGraph_fderiv hu]
  simp [dotProduct,Fin.sum_univ_succ]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_minimal_surface_graph_chart
