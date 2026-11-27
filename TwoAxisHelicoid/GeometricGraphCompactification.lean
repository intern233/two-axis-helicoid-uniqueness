import TwoAxisHelicoid.ProvedPlaneUniformization
import TwoAxisHelicoid.PhysicalGraphPunctureFilling
import TwoAxisHelicoid.PhysicalGraphPuncturePoleOrders
import TwoAxisHelicoid.ComplexEndCompactification
import TwoAxisHelicoid.PunctureCircleResidue

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology InnerProductSpace
open scoped Topology Manifold ContDiff
universe u

/-- The puncture filling and the flux-to-poles implication depend only
on the actual closed embedding, its harmonic conformal coordinates and
its physical graph end. -/
theorem harmonic_graph_compactification {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (charts : ∀ e∈atlas ℂ M, HarmonicImmersionChart X e)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    ∃ E : PuncturedComplexEnd M, E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧
        (let _ := compactifiedEndAtlas E
         IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
           ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M)) ∧
        let Y := X ∘ E.coord.symm
        (∀ j : Fin 3, ∀ ε : ℝ, 0<ε → ∃ r∈Ioo (0:ℝ) ε,
          (∮ z in C(0,r), immersionComplexCoefficient Y z j).im=0) →
        (MeromorphicAt (fun z => immersionComplexCoefficient Y z 2) 0 ∧
          meromorphicOrderAt (fun z => immersionComplexCoefficient Y z 2) 0=(-2:ℤ)) ∧
        MeromorphicAt (immersionGaussLogDerivative Y) 0 ∧
          meromorphicOrderAt (immersionGaussLogDerivative Y) 0=(-2:ℤ) := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ℂ M
  obtain ⟨E,hol⟩ := physical_helicoid_graph_holomorphic_filling closed charts graph topological_plane_uniformization_proved
  refine ⟨E,hol,⟨compactifiedEndAtlas_isManifold E hol,compactifiedEnd_inclusion_contMDiff E⟩,?_⟩
  intro Y flux
  have good := harmonic_immersion_chart_maximal charts hol
  have regular : ∀ᶠ z in 𝓝[≠] (0:ℂ), (∀ j, HarmonicAt (fun w => Y w j) z) ∧
      ConformalCoordinateDerivatives Y z ∧ Function.Injective (fderiv ℝ Y z) := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) E.radius_pos)] with z nz near
    exact good z (E.mem_target_of_ball_ne near nz)
  apply physical_graph_puncture_double_poles X closed.isProperMap graph E regular
  intro j
  exact harmonic_puncture_primitive_of_peripheral_flux (regular.mono fun z hz => hz.1 j) (flux j)

/-- For an oriented smooth minimal embedding of any genus the physical
helicoidal C¹ graph gives the complex structure on its actual one-point
compactification. In this same puncture chart, zero spatial conormal
flux on arbitrarily small circles suffices for the two physical double
poles. The compactification itself uses no flux hypothesis. -/
theorem oriented_minimal_graph_compactification {M : Type u} [TopologicalSpace M]
    [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M] [NoncompactSpace M]
    (X : M → Fin 3 → ℝ) (closed : IsClosedEmbedding X)
    (smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (immersion : ∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X q))
    (orientation : PositiveSurfaceAtlas M)
    (minimal : ∀ q, coordinateMeanCurvature (X ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q)=0)
    (graph : HasHelicoidC1End (coordinateToTube ∘ X)) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ d∈atlas ℂ M, HarmonicImmersionChart X d) ∧
      ∃ E : PuncturedComplexEnd M, E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M ∧
        (let _ := compactifiedEndAtlas E
         IsManifold 𝓘(ℂ,ℂ) ω (OnePoint M) ∧
           ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (OnePoint.some : M → OnePoint M)) ∧
        let Y := X ∘ E.coord.symm
        (∀ j : Fin 3, ∀ ε : ℝ, 0<ε → ∃ r∈Ioo (0:ℝ) ε,
          (∮ z in C(0,r), immersionComplexCoefficient Y z j).im=0) →
        (MeromorphicAt (fun z => immersionComplexCoefficient Y z 2) 0 ∧
          meromorphicOrderAt (fun z => immersionComplexCoefficient Y z 2) 0=(-2:ℤ)) ∧
        MeromorphicAt (immersionGaussLogDerivative Y) 0 ∧
          meromorphicOrderAt (immersionGaussLogDerivative Y) 0=(-2:ℤ) := by
  obtain ⟨S,man,charts⟩ := oriented_minimal_induced_harmonic_atlas smooth immersion orientation minimal
  let _ := S
  let _ := man
  exact ⟨S,man,charts,harmonic_graph_compactification X closed charts graph⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_graph_compactification
#print axioms TwoAxisHelicoid.oriented_minimal_graph_compactification
