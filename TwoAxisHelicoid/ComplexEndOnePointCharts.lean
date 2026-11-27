import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Normed.Group.Bounded

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology OnePoint ContDiff Manifold
set_option maxHeartbeats 1300000

variable {M : Type*} [TopologicalSpace M]

/-- A finite chart, transported by the canonical inclusion of the
original surface into its one-point compactification. -/
noncomputable def finiteOnePointChart (e : OpenPartialHomeomorph M ℂ) :
    OpenPartialHomeomorph (OnePoint M) ℂ where
  toFun p := p.elim 0 e
  invFun z := (e.symm z : OnePoint M)
  source := OnePoint.some '' e.source
  target := e.target
  map_source' := by rintro _ ⟨x,hx,rfl⟩; exact e.map_source hx
  map_target' := fun z hz => ⟨e.symm z,e.map_target hz,rfl⟩
  left_inv' := by rintro _ ⟨x,hx,rfl⟩; exact congrArg OnePoint.some (e.left_inv hx)
  right_inv' := fun z hz => e.right_inv hz
  open_source := OnePoint.isOpen_image_coe.mpr e.open_source
  open_target := e.open_target
  continuousOn_toFun := by
    rintro _ ⟨x,hx,rfl⟩
    apply ContinuousAt.continuousWithinAt
    apply OnePoint.continuousAt_coe.mpr
    exact e.continuousAt hx
  continuousOn_invFun := fun z hz =>
    (OnePoint.continuous_coe.continuousAt.comp (e.symm.continuousAt hz)).continuousWithinAt

theorem finiteOnePointChart_coe_source (e : OpenPartialHomeomorph M ℂ) (x : M) :
    (x : OnePoint M) ∈ (finiteOnePointChart e).source ↔ x ∈ e.source :=
  OnePoint.coe_injective.mem_set_image

/-- A punctured conformal end coordinate at the topology's unique
infinite end. The two limits describe its two directions as an end
coordinate. The complementary core is compact. -/
structure PuncturedComplexEnd (M : Type*) [TopologicalSpace M] where
  coord : OpenPartialHomeomorph M ℂ
  radius : ℝ
  radius_pos : 0 < radius
  target_eq : coord.target = Metric.ball (0 : ℂ) radius \ {0}
  compact_core : IsCompact coord.sourceᶜ
  to_zero : Tendsto coord (cocompact M) (𝓝 0)
  from_zero : Tendsto coord.symm (𝓝[≠] 0) (cocompact M)

namespace PuncturedComplexEnd

variable (E : PuncturedComplexEnd M)

theorem coord_ne_zero {x : M} (hx : x ∈ E.coord.source) : E.coord x ≠ 0 := by
  have hh := E.coord.map_source hx
  rw [E.target_eq] at hh
  exact hh.2

theorem mem_target_of_ball_ne {w : ℂ} (hw : w ∈ Metric.ball (0:ℂ) E.radius) (hn : w ≠ 0) : w ∈ E.coord.target :=
  E.target_eq ▸ ⟨hw,hn⟩

noncomputable def filledInverse (w : ℂ) : OnePoint M :=
  if w = 0 then ∞ else (E.coord.symm w : OnePoint M)

theorem filledInverse_continuousAt [T2Space M] {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) E.radius) :
    ContinuousAt E.filledInverse w := by
  by_cases hz : w = 0
  · subst w
    rw [continuousAt_iff_punctured_nhds]
    have ht : Tendsto (fun v => (E.coord.symm v : OnePoint M)) (𝓝[≠] 0) (𝓝 ∞) :=
      (Filter.coclosedCompact_eq_cocompact (X := M) ▸ OnePoint.tendsto_coe_infty).comp E.from_zero
    have he : E.filledInverse =ᶠ[𝓝[≠] 0] fun v => (E.coord.symm v : OnePoint M) := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      simp [filledInverse,show v ≠ 0 from hv]
    rw [show E.filledInverse 0 = (OnePoint.infty : OnePoint M) from by simp [filledInverse]]
    exact ht.congr' he.symm
  · have hc : w ∈ E.coord.target := E.target_eq ▸ ⟨hw,hz⟩
    have he : E.filledInverse =ᶠ[𝓝 w] fun v => (E.coord.symm v : OnePoint M) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with v hv
      simp [filledInverse,show v ≠ 0 from hv]
    exact (OnePoint.continuous_coe.continuousAt.comp (E.coord.symm.continuousAt hc)).congr_of_eventuallyEq he

/-- The punctured coordinate extends to a local homeomorphism at the
compactifying point, with value zero and an entire open disk as target. -/
noncomputable def filledChart [T2Space M] : OpenPartialHomeomorph (OnePoint M) ℂ where
  toFun p := p.elim 0 E.coord
  invFun := E.filledInverse
  source := (OnePoint.some '' E.coord.sourceᶜ)ᶜ
  target := Metric.ball 0 E.radius
  map_source' := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact Metric.mem_ball_self E.radius_pos
    | coe x =>
      have hx : x ∈ E.coord.source := by simpa [OnePoint.coe_injective.mem_set_image] using hp
      have ht := E.coord.map_source hx
      rw [E.target_eq] at ht
      exact ht.1
  map_target' := by
    intro w hw
    by_cases hz : w = 0
    · subst w
      simp [filledInverse]
    · have hsrc := E.coord.map_target (E.mem_target_of_ball_ne hw hz)
      simpa [filledInverse,hz,OnePoint.coe_injective.mem_set_image] using hsrc
  left_inv' := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => simp [filledInverse]
    | coe x =>
      have hx : x ∈ E.coord.source := by simpa [OnePoint.coe_injective.mem_set_image] using hp
      simp [filledInverse,E.coord_ne_zero hx,E.coord.left_inv hx]
  right_inv' := by
    intro w hw
    by_cases hz : w = 0
    · simp [filledInverse,hz]
    · simp [filledInverse,hz,E.coord.right_inv (E.mem_target_of_ball_ne hw hz)]
  open_source := OnePoint.isOpen_compl_image_coe.mpr ⟨E.coord.open_source.isClosed_compl,E.compact_core⟩
  open_target := Metric.isOpen_ball
  continuousOn_toFun := by
    intro p hp
    cases p using OnePoint.rec with
    | infty =>
      apply ContinuousAt.continuousWithinAt
      apply OnePoint.continuousAt_infty'.mpr
      change Tendsto E.coord (coclosedCompact M) (𝓝 0)
      rw [Filter.coclosedCompact_eq_cocompact]
      exact E.to_zero
    | coe x =>
      have hx : x ∈ E.coord.source := by simpa [OnePoint.coe_injective.mem_set_image] using hp
      apply ContinuousAt.continuousWithinAt
      apply OnePoint.continuousAt_coe.mpr
      exact E.coord.continuousAt hx
  continuousOn_invFun := fun _ hw => (E.filledInverse_continuousAt hw).continuousWithinAt

end PuncturedComplexEnd
end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.PuncturedComplexEnd.filledChart
