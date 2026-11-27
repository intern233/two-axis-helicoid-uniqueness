import TwoAxisHelicoid.ReflectedPuncturePrimitives
import TwoAxisHelicoid.OriginalSurfaceSchwarz
import TwoAxisHelicoid.AntiholomorphicPunctureGerm

namespace TwoAxisHelicoid
open Complex Set Filter Metric Topology
open scoped Topology ComplexConjugate ContDiff Manifold

/-- A single antiholomorphic reflection reversing one actual Cartesian
coordinate cancels its entire peripheral flux, with no assumption on
the order or meromorphicity of the coordinate differential at the end. -/
theorem reflected_spatial_coordinate_has_puncture_primitive {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {X : M → Fin 3 → ℝ}
    (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d) (E : PuncturedComplexEnd M)
    (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) (j : Fin 3) (f : M ≃ₜ M)
    (anti : AntiholomorphicInSurfaceCharts f) (inv : Function.Involutive f) (flips : ∀ p, X (f p) j= -X p j) :
    let Y := X ∘ E.coord.symm
    ∃ H : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (immersionComplexCoefficient Y z j) z ∧ (H z).re=Y z j := by
  intro Y
  obtain ⟨v,va,vz,vn,act⟩ := antiholomorphic_involution_at_puncture E f inv (anti _ _ hol hol)
  have target : E.coord.target∈𝓝[≠] (0:ℂ) := by
    rw [E.target_eq]
    exact inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) E.radius_pos)) self_mem_nhdsWithin
  have germ := harmonic_immersion_chart_maximal charts hol
  apply reflected_odd_harmonic_has_end_primitive (y := fun z => Y z j) (u := v)
    (Filter.mem_of_superset target (fun z hz => (germ z hz).1 j)) va vz vn
  filter_upwards [act] with z hz
  change X (E.coord.symm (v z)) j= -X (E.coord.symm (conj z)) j
  rw [hz.2,flips]

/-- All three Cartesian differentials on an arbitrary-genus embedded
two-axis surface have single-valued complex potentials around its
one conformal puncture. Both spatial Schwarz actions are deduced from
the complete straight lines. No singularity order is required. -/
theorem two_axis_spatial_coordinates_have_end_primitives {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] [PreconnectedSpace M] {X : M → Fin 3 → ℝ}
    (embedded : IsClosedEmbedding X) (charts : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (horizontal : ∀ s : ℝ, (![s,0,0] : Fin 3 → ℝ)∈range X)
    (vertical : ∀ s : ℝ, (![0,0,s] : Fin 3 → ℝ)∈range X)
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M) :
    let Y := X ∘ E.coord.symm
    ∀ j : Fin 3, ∃ H : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (immersionComplexCoefficient Y z j) z ∧ (H z).re=Y z j := by
  intro Y j
  obtain ⟨h,ah,ih,mh⟩ := horizontal_schwarz_on_original_surface embedded charts horizontal
  obtain ⟨v,av,iv,mv⟩ := vertical_schwarz_on_original_surface embedded charts vertical
  fin_cases j
  · exact reflected_spatial_coordinate_has_puncture_primitive charts E hol 0 v av iv (fun p => congrFun (mv p) 0)
  · exact reflected_spatial_coordinate_has_puncture_primitive charts E hol 1 h ah ih (fun p => congrFun (mh p) 1)
  · exact reflected_spatial_coordinate_has_puncture_primitive charts E hol 2 h ah ih (fun p => congrFun (mh p) 2)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.two_axis_spatial_coordinates_have_end_primitives
