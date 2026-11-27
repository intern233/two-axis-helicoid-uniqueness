import TwoAxisHelicoid.ImmersionAtlas
import Mathlib.Geometry.Manifold.ImmersionDiff

namespace TwoAxisHelicoid
open Set Topology
open scoped Topology ContDiff Manifold

variable {M E A : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The image atlas makes the actual ambient map smooth, with no
assumption of compatibility with a preexisting compactification atlas. -/
theorem immersionAtlas_map_contMDiff (F : M → A) (hF : Continuous F)
    (hcover : ∀ x : M, ∃ e : OpenPartialHomeomorph M E,
      RegularImmersionChart F e ∧ x ∈ e.source) :
    let _ := immersionAtlasChartedSpace F hcover
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,A) ∞ F := by
  let _ := immersionAtlasChartedSpace F hcover
  dsimp only
  intro x
  have he : RegularImmersionChart F (chartAt E x) := chart_mem_atlas E x
  have hx : chartAt E x x ∈ (chartAt E x).target :=
    (chartAt E x).map_source (mem_chart_source E x)
  apply contMDiffAt_iff.mpr
  refine ⟨hF.continuousAt,?_⟩
  simpa only [mfld_simps] using!
    (he _ hx).1.contDiffWithinAt (s := range 𝓘(ℝ,E))

theorem immersionAtlas_map_hasMFDerivAt (F : M → A) (hF : Continuous F)
    (hcover : ∀ x : M, ∃ e : OpenPartialHomeomorph M E,
      RegularImmersionChart F e ∧ x ∈ e.source) :
    let _ := immersionAtlasChartedSpace F hcover
    ∀ x, HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,A) F x
      (fderiv ℝ (F ∘ (chartAt E x).symm) (chartAt E x x)) := by
  let _ := immersionAtlasChartedSpace F hcover
  dsimp only
  intro x
  have he : RegularImmersionChart F (chartAt E x) := chart_mem_atlas E x
  have hx : chartAt E x x ∈ (chartAt E x).target :=
    (chartAt E x).map_source (mem_chart_source E x)
  have hd := ((he _ hx).1.differentiableAt (by simp)).hasFDerivAt
  refine ⟨hF.continuousAt,?_⟩
  simpa only [writtenInExtChartAt,mfld_simps] using!
    hd.hasFDerivWithinAt (s := range 𝓘(ℝ,E))

/-- The derivative of the ambient map is injective in the newly
constructed atlas, including every newly added chart. -/
theorem immersionAtlas_map_mfderiv_injective (F : M → A) (hF : Continuous F)
    (hcover : ∀ x : M, ∃ e : OpenPartialHomeomorph M E,
      RegularImmersionChart F e ∧ x ∈ e.source) :
    let _ := immersionAtlasChartedSpace F hcover
    ∀ x, Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,A) F x) := by
  let _ := immersionAtlasChartedSpace F hcover
  dsimp only
  intro x
  rw [(immersionAtlas_map_hasMFDerivAt F hF hcover x).mfderiv]
  have he : RegularImmersionChart F (chartAt E x) := chart_mem_atlas E x
  exact (he _ ((chartAt E x).map_source (mem_chart_source E x))).2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.immersionAtlas_map_contMDiff
#print axioms TwoAxisHelicoid.immersionAtlas_map_mfderiv_injective
