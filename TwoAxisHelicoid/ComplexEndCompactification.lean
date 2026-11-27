import TwoAxisHelicoid.ComplexEndOnePointCharts
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology OnePoint ContDiff Manifold
set_option maxHeartbeats 1500000

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M]
variable (E : PuncturedComplexEnd M)

@[instance_reducible] noncomputable def compactifiedEndAtlas : ChartedSpace ℂ (OnePoint M) where
  atlas := {d | (∃ e ∈ atlas ℂ M, d = finiteOnePointChart e) ∨ d = E.filledChart}
  chartAt := OnePoint.rec E.filledChart (fun x => finiteOnePointChart (chartAt ℂ x))
  mem_chart_source p := by
    cases p using OnePoint.rec with
    | infty => exact OnePoint.infty_notMem_image_coe
    | coe x => exact (finiteOnePointChart_coe_source _ _).mpr (mem_chart_source ℂ x)
  chart_mem_atlas p := by
    cases p using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe x => exact Or.inl ⟨_,chart_mem_atlas ℂ x,rfl⟩

omit [ChartedSpace ℂ M] in
theorem compactifiedEndChart_coe_source (x : M) : (x:OnePoint M) ∈ E.filledChart.source ↔ x ∈ E.coord.source := by
  change (x:OnePoint M) ∉ OnePoint.some '' E.coord.sourceᶜ ↔ _
  simp [OnePoint.coe_injective.mem_set_image]

omit [T2Space M] in
theorem complexAtlas_realized_transition {e d : OpenPartialHomeomorph M ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {z : ℂ} (hz : z ∈ (e.symm.trans d).source) :
    ContDiffAt ℂ ω (e.symm.trans d) z := by
  have h : ContDiffOn ℂ ω (e.symm.trans d) (e.symm.trans d).source := by
    simpa only [mfld_simps] using! (𝓘(ℂ,ℂ)).contDiffOn_extendCoordChange he hd
  exact h.contDiffAt ((e.symm.trans d).open_source.mem_nhds hz)

/-- A holomorphic punctured-disk chart of the actual end fills in to a
complex analytic atlas on the compactification of the original space. -/
theorem compactifiedEndAtlas_isManifold [IsManifold 𝓘(ℂ,ℂ) ω M]
    (hE : E.coord ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    let _ := compactifiedEndAtlas E
    IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) := by
  let _ := compactifiedEndAtlas E
  apply isManifold_of_contDiffOn
  intro e d he hd z hz
  have hdom : z ∈ (e.symm.trans d).source := hz.1
  change ContDiffWithinAt ℂ ω (e.symm.trans d) _ z
  apply ContDiffAt.contDiffWithinAt
  rcases he with ⟨e',he',rfl⟩ | rfl <;> rcases hd with ⟨d',hd',rfl⟩ | rfl
  · have hsrc : e'.symm z ∈ d'.source := (finiteOnePointChart_coe_source _ _).mp hdom.2
    exact complexAtlas_realized_transition (IsManifold.subset_maximalAtlas he') (IsManifold.subset_maximalAtlas hd')
      (show z ∈ (e'.symm.trans d').source from ⟨hdom.1,hsrc⟩)
  · have hsrc : e'.symm z ∈ E.coord.source := (compactifiedEndChart_coe_source E _).mp hdom.2
    exact complexAtlas_realized_transition (IsManifold.subset_maximalAtlas he') hE
      (show z ∈ (e'.symm.trans E.coord).source from ⟨hdom.1,hsrc⟩)
  · have hn : z ≠ 0 := by
      intro hz'
      subst z
      have h0 : E.filledInverse 0 ∈ (finiteOnePointChart d').source := hdom.2
      simp [PuncturedComplexEnd.filledInverse] at h0
      exact OnePoint.infty_notMem_image_coe h0
    have hball : z ∈ Metric.ball (0:ℂ) E.radius := hdom.1
    have he0 : E.filledInverse z = (E.coord.symm z : OnePoint M) := by simp [PuncturedComplexEnd.filledInverse,hn]
    have hd1 : E.filledInverse z ∈ (finiteOnePointChart d').source := hdom.2
    rw [he0] at hd1
    have hsrc : z ∈ (E.coord.symm.trans d').source :=
      ⟨E.target_eq ▸ ⟨hball,hn⟩,(finiteOnePointChart_coe_source _ _).mp hd1⟩
    apply (complexAtlas_realized_transition hE (IsManifold.subset_maximalAtlas hd') hsrc).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hn] with v hv
    change (E.filledInverse v).elim 0 d' = d' (E.coord.symm v)
    rw [show E.filledInverse v = (E.coord.symm v : OnePoint M) from by simp [PuncturedComplexEnd.filledInverse,show v ≠ 0 from hv]]
    rfl
  · apply (contDiffAt_id (n := ω) (𝕜 := ℂ)).congr_of_eventuallyEq
    filter_upwards [E.filledChart.open_target.mem_nhds hdom.1] with v hv
    exact E.filledChart.right_inv hv

/-- The inclusion of the original Riemann surface into the filled
surface is complex analytic on its entire original domain. -/
theorem compactifiedEnd_inclusion_contMDiff [IsManifold 𝓘(ℂ,ℂ) ω M]
    (E : PuncturedComplexEnd M) :
    let _ := compactifiedEndAtlas E
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M) := by
  let _ := compactifiedEndAtlas E
  change ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M)
  intro x
  let e := chartAt ℂ x
  have hx := mem_chart_source ℂ x
  have htr : ((e : M → ℂ) ∘ e.symm) =ᶠ[𝓝 (e x)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with w hw
    exact e.right_inv hw
  apply contMDiffAt_iff.mpr
  refine ⟨OnePoint.continuous_coe.continuousAt,?_⟩
  exact ((contDiffAt_id (n := ω) (𝕜 := ℂ)).congr_of_eventuallyEq htr).contDiffWithinAt

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compactifiedEndAtlas_isManifold
#print axioms TwoAxisHelicoid.compactifiedEnd_inclusion_contMDiff
