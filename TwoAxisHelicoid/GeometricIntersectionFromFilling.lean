import TwoAxisHelicoid.PublishedGeometricClassification
import TwoAxisHelicoid.MarkedHelicoidIntersectionTheorem
import TwoAxisHelicoid.FilledRhombicMarking
import TwoAxisHelicoid.MarkedSpatialDisks

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold OnePoint
set_option maxHeartbeats 1800000

/-- A holomorphic puncture of the original harmonic conformal surface,
together with compact genus-one uniformization, places its actual two
straight axes in a rhombic marking. Spatial coordinates and the
prescribed asymptotic helicoid are unaffected by this change of domain. -/
theorem conformally_filled_two_axes_intersection_and_disks {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ,ℂ) ω M] {L₀ : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L₀)
    (uniform : CompactGenusOneUniformization.{0} L₀)
    (X : M → Fin 3 → ℝ) (hX : IsClosedEmbedding X) (hchart : ∀ d∈atlas ℂ M, HarmonicImmersionChart X d)
    (E : PuncturedComplexEnd M) (hol : E.coord∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M)
    {α : ℝ} (hα : α≠0) (b : ℝ)
    (horizontal : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ)∈range X)
    (vertical : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range X)
    (endGraph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,b] ∘ X))
    (aligned : (axisSpatialNormalization hα ![0,0,b]) ⁻¹' range (fun w : ℂ => standardHelicoid w.re w.im)=range (axisRuledHelicoid I α 0)) :
    (range X ∩ range (axisRuledHelicoid I α 0)={P | (P 1=0 ∧ P 2=0) ∨ (P 0=0 ∧ P 1=0)}) ∧
      HasSpatialTwoDiskPartition (range X) α := by
  obtain ⟨t,ht,Z,hZ,g,eq⟩ := conformally_filled_actual_rhombic_marking top uniform X hX hchart E hol horizontal vertical
  let F := harmonicTorusImmersion hZ
  change X ∘ g.symm=F at eq
  have ranges : range F=range X := by rw [← eq,g.symm.surjective.range_comp]
  have embedded : IsClosedEmbedding F := by rw [← eq]; exact hX.comp g.symm.isClosedEmbedding
  have graph := endGraph.comp_homeomorph g.symm
  have form : (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,b] ∘ X) ∘ g.symm=
      coordinateToTube ∘ axisSpatialNormalization hα ![0,0,b] ∘ F := by
    exact congrArg (fun U => (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,b]) ∘ U) eq
  rw [form] at graph
  have res := marked_rhombic_helicoid_intersection ht hZ hα b embedded
    (fun r => ranges.symm ▸ horizontal r) (fun r => ranges.symm ▸ vertical r) graph aligned
  change range F ∩ _ = _ at res
  rw [aligned] at res
  refine ⟨ranges ▸ res,?_⟩
  rw [← ranges]
  apply marked_two_disk_partition ht hZ embedded.isEmbedding
  intro z hz on
  have inX : Z z∈range F := by
    rw [show F=harmonicTorusImmersion hZ from rfl,harmonicTorusImmersion_range]
    exact ⟨z,hz,rfl⟩
  exact (Set.ext_iff.mp res (Z z)).mp ⟨inX,on⟩

/-- The unmarked geometric intersection statement follows from the
published end compactification and classical uniformization. The
comparison result itself is proved on the original spatial image. -/
theorem geometric_two_axis_intersection_from_end_uniformization
    (bbc : PublishedOneHandleEndTheorem) (poincare : SimplyConnectedNoncompactUniformization.{0}) :
    GeometricTwoAxisIntersectionTheorem := by
  intro s α hα b A H complete _ horizontal vertical endGraph aligned
  obtain ⟨D⟩ := bbc s complete s.one_topological_end s.image_ne_embedded_plane
  obtain ⟨S,hm,hc,E,hol⟩ := published_poles_original_holomorphic_puncture s D
  let _ := S
  have manifold : IsManifold 𝓘(ℂ,ℂ) ω s.carrier := hm
  rw [aligned]
  exact (conformally_filled_two_axes_intersection_and_disks s.topologicalType (compact_genus_one_uniformization_of_classical poincare _)
    s.position s.closedEmbedding hc E hol hα b horizontal vertical endGraph aligned).1

/-- Proposition 2.2 including the two actual open disks, their opposite
sides and the Euclidean half-turn interchanging them. -/
theorem geometric_two_axis_open_disks (s : OriginalSmoothHelicoid) (bbc : PublishedOneHandleEndTheorem)
    (poincare : SimplyConnectedNoncompactUniformization.{0}) {α : ℝ} (hα : α≠0) (b : ℝ)
    (horizontal : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ)∈range s.position)
    (vertical : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range s.position)
    (endGraph : HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,b] ∘ s.position))
    (aligned : (axisSpatialNormalization hα ![0,0,b]) ⁻¹' range (fun w : ℂ => standardHelicoid w.re w.im)=range (axisRuledHelicoid I α 0)) :
    (range s.position ∩ range (axisRuledHelicoid I α 0)={P | (P 1=0 ∧ P 2=0) ∨ (P 0=0 ∧ P 1=0)}) ∧
      HasSpatialTwoDiskPartition (range s.position) α := by
  obtain ⟨D⟩ := bbc s s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
  obtain ⟨S,hm,hc,E,hol⟩ := published_poles_original_holomorphic_puncture s D
  let _ := S
  have manifold : IsManifold 𝓘(ℂ,ℂ) ω s.carrier := hm
  exact conformally_filled_two_axes_intersection_and_disks s.topologicalType (compact_genus_one_uniformization_of_classical poincare _)
    s.position s.closedEmbedding hc E hol hα b horizontal vertical endGraph aligned

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.conformally_filled_two_axes_intersection_and_disks
#print axioms TwoAxisHelicoid.geometric_two_axis_intersection_from_end_uniformization
#print axioms TwoAxisHelicoid.geometric_two_axis_open_disks
