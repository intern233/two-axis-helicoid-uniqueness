import TwoAxisHelicoid.CompactGenusOneUniformizationInput

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Manifold ContDiff

universe u

/-- The noncompact case of the classical uniformization theorem on
abstract Hausdorff second-countable Riemann surfaces. -/
def SimplyConnectedNoncompactUniformization : Prop :=
  ∀ (P : Type u) [TopologicalSpace P] [T2Space P] [SecondCountableTopology P]
    [ChartedSpace ℂ P] [IsManifold 𝓘(ℂ,ℂ) ω P] [SimplyConnectedSpace P] [NoncompactSpace P],
      Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) P ℂ ω) ∨
      Nonempty (Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) P RiemannUnitDisk ω)

/-- The classical theorem applies to the actual pulled-back complex
plane atlas. The topological marking supplies simple connectivity,
noncompactness, separation, and second countability. -/
theorem topological_plane_uniformization_of_classical
    (uni : SimplyConnectedNoncompactUniformization.{u}) : TopologicalPlaneUniformization.{u} := by
  intro P _ _ _ h
  obtain ⟨E⟩ := h
  have ht : T2Space P := E.isEmbedding.t2Space
  have hs : SecondCountableTopology P := E.isEmbedding.secondCountableTopology
  have hc : ContractibleSpace P := E.contractibleSpace
  have hn : NoncompactSpace P := ⟨fun hcompact => noncompact_univ ℂ (by
    simpa only [image_univ,E.surjective.range_eq] using hcompact.image E.continuous)⟩
  exact uni P

theorem compact_genus_one_uniformization_of_classical
    (uni : SimplyConnectedNoncompactUniformization.{u}) (L : PeriodPair) : CompactGenusOneUniformization.{u} L :=
  genus_one_uniformization_input_of_plane_dichotomy (topological_plane_uniformization_of_classical uni) L

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_genus_one_uniformization_of_classical
