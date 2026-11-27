import TwoAxisHelicoid.TopologicalSurfaceNormal
import TwoAxisHelicoid.HolomorphicCoverPullback
import TwoAxisHelicoid.OrientedMinimalHarmonicAtlas
import TwoAxisHelicoid.ActualTorusManifoldImmersion

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology Manifold ContDiff

/-- A purely topological punctured torus provides a reference atlas with
positive local degree transitions. Smoothness in any preassigned
real atlas plays no role in the marking. -/
theorem topological_punctured_torus_positive_degree_atlas {M : Type*} [TopologicalSpace M]
    {L : PeriodPair} (h : M ≃ₜ PuncturedPeriodTorus L) :
    ∃ d : M → OpenPartialHomeomorph M ℂ, (∀ x, x ∈ (d x).source) ∧
      ∀ x y z, z ∈ (d x).source → z ∈ (d y).source → planeChartIndex (d x) (d y) z = 1 := by
  let _ := holomorphicCoverAtlas h.isLocalHomeomorph
  have hm : IsManifold 𝓘(ℂ,ℂ) ω M := holomorphicCoverAtlas_isManifold h.isLocalHomeomorph
  exact ⟨chartAt ℂ,mem_chart_source ℂ,fun x y _ hx hy => planeChartIndex_holomorphic
    (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)) (IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ y)) hx hy⟩

/-- A smooth real minimal immersion of a surface merely homeomorphic to a
once-punctured torus has an actual induced complex analytic harmonic atlas.
The topological marking need not be a smooth map, and the preferred real
charts need not be consistently oriented. -/
theorem punctured_torus_minimal_induced_oriented_atlas {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    {F : M → Fin 3 → ℝ} (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F x))
    (hm : ∀ x : M, coordinateMeanCurvature (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0) :
    ∃ N : M → Fin 3 → ℝ, Continuous N ∧ ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ ∀ e ∈ atlas ℂ M, OrientedIsothermalChart F N e ∧ HarmonicImmersionChart F e := by
  obtain ⟨d,hd,hpos⟩ := topological_punctured_torus_positive_degree_atlas top
  have hr := smooth_surface_regular_manifold_chart hF hi
  obtain ⟨N,hN,ht⟩ := surface_transverse_field_of_topological_atlas (chartAt ℂ) d (mem_chart_source ℂ) hd hr hpos
  have hconv {e : OpenPartialHomeomorph M ℂ} (hh : OrientedIsothermalChart F N e) : HarmonicImmersionChart F e :=
    oriented_isothermal_chart_actual_harmonic hr hm hh
  obtain ⟨S,hS,hs⟩ := smooth_minimal_manifold_induced_complex_structure hF hi hN hm ht
  exact ⟨N,hN,S,hS,fun e he => ⟨hs e he,hconv (hs e he)⟩⟩

theorem punctured_torus_minimal_induced_harmonic_atlas {M : Type*} [TopologicalSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    {F : M → Fin 3 → ℝ} (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F x))
    (hm : ∀ x : M, coordinateMeanCurvature (F ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ ∀ e ∈ atlas ℂ M, HarmonicImmersionChart F e := by
  obtain ⟨_,_,S,hS,hs⟩ := punctured_torus_minimal_induced_oriented_atlas top hF hi hm
  exact ⟨S,hS,fun e he => (hs e he).2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_torus_minimal_induced_harmonic_atlas
