import TwoAxisHelicoid.SmoothImmersionLeftInverse
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

variable {M E A : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

/-- A genuine topological chart whose inverse parametrizes the ambient
image smoothly with injective derivative. -/
def RegularImmersionChart (F : M → A) (e : OpenPartialHomeomorph M E) : Prop :=
  ∀ y ∈ e.target, ContDiffAt ℝ ∞ (F ∘ e.symm) y ∧
    Function.Injective (fderiv ℝ (F ∘ e.symm) y)

/-- Compatibility is proved from the actual ambient parametrizations,
rather than asserted as extra gluing data. -/
theorem regularImmersionChart_transition {F : M → A}
    {e e' : OpenPartialHomeomorph M E} (he : RegularImmersionChart F e)
    (he' : RegularImmersionChart F e') {y : E} (hy : y ∈ (e.symm.trans e').source) :
    ContDiffAt ℝ ∞ (e.symm.trans e') y := by
  have hyy : (e.symm.trans e') y ∈ e'.target := e'.map_source hy.2
  obtain ⟨hf,hfi⟩ := he' _ hyy
  have heq : (F ∘ e'.symm) ∘ (e.symm.trans e') =ᶠ[𝓝 y] F ∘ e.symm := by
    filter_upwards [(e.symm.trans e').open_source.mem_nhds hy] with z hz
    exact congrArg F (e'.left_inv hz.2)
  have hcomp : ContDiffAt ℝ ∞ ((F ∘ e'.symm) ∘ (e.symm.trans e')) y :=
    (he y hy.1).1.congr_of_eventuallyEq heq
  exact contDiffAt_of_comp_immersion hf hfi ((e.symm.trans e').continuousAt hy) hcomp

@[instance_reducible] noncomputable def immersionAtlasChartedSpace (F : M → A)
    (hcover : ∀ x : M, ∃ e : OpenPartialHomeomorph M E, RegularImmersionChart F e ∧ x ∈ e.source) :
    ChartedSpace E M where
  atlas := {e | RegularImmersionChart F e}
  chartAt x := (hcover x).choose
  mem_chart_source x := (hcover x).choose_spec.2
  chart_mem_atlas x := (hcover x).choose_spec.1

theorem immersionAtlas_isManifold (F : M → A)
    (hcover : ∀ x : M, ∃ e : OpenPartialHomeomorph M E, RegularImmersionChart F e ∧ x ∈ e.source) :
    let _ := immersionAtlasChartedSpace F hcover
    IsManifold 𝓘(ℝ,E) ∞ M := by
  let _ := immersionAtlasChartedSpace F hcover
  apply isManifold_of_contDiffOn
  intro e e' he he' y hy
  exact (regularImmersionChart_transition he he' hy.1).contDiffWithinAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.regularImmersionChart_transition
#print axioms TwoAxisHelicoid.immersionAtlas_isManifold

