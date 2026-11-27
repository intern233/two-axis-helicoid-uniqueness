import TwoAxisHelicoid.ActualConverseImmersion
import TwoAxisHelicoid.OriginalPositionalHelicoid
import TwoAxisHelicoid.PublishedGeometricClassification
import TwoAxisHelicoid.CertifiedCompactDoublePoints

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped ContDiff Manifold Topology

/-- Global injectivity alone turns the same centered period solution into an
original smooth embedded representative, with the crossing at the origin,
the two prescribed lines and the normal graph over its specified helicoid. -/
theorem certified_original_representative_of_injective
    (hi : Function.Injective certifiedTorusImmersion) :
    ∃ s : OriginalHelicoidRepresentative,
      s.image = range (centeredActualEuclideanImmersion certifiedClosedParameters.height_pos
        certifiedClosedParameters.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
        certifiedClosedParameters.vertical_closed certifiedClosedParameters.horizontal_closed) ∧
      s.axes.horizontalPoint = 0 ∧ s.axes.horizontalDirection = 1 ∧
      s.axes.pitch = 2*(certifiedClosedParameters.a-1)/1 := by
  let p := certifiedClosedParameters
  let X := centeredActualTorusImmersion p.height_pos p.abscissa_mem (by norm_num : (1:ℝ) ≠ 0)
    p.vertical_closed p.horizontal_closed
  let H := certified_converse_immersion
  have hinj : Function.Injective X := by
    intro x y h
    apply hi
    apply congrArg coordinateToEuclidean
    have eq := congrArg (fun v : Fin 3 → ℝ => v+actualGlobalImmersion p.t p.a 1 p.height_pos 1) h
    simpa only [X,centeredActualTorusImmersion,sub_add_cancel] using eq
  have he : IsClosedEmbedding X := IsClosedEmbedding.of_continuous_injective_isClosedMap
    H.proper.continuous hinj H.proper.isClosedMap
  have hx (r : ℝ) : r • (![1,0,0] : Fin 3 → ℝ) = ![r,0,0] := by
    ext j
    fin_cases j <;> simp
  let α := 2*(p.a-1)/1
  have hα : α ≠ 0 := certified_normalization_scale_ne_zero
  let axes : OriginalHelicoidAxes (range X) := {
    horizontalDirection := 1, unit := norm_one, horizontalPoint := 0
    horizontal := fun r => by
      change (0 : Fin 3 → ℝ) + r • ![1,0,0] ∈ range X
      rw [zero_add,hx]
      obtain ⟨q,hq⟩ := H.horizontal_axis r
      exact ⟨q,hq⟩
    vertical := H.vertical_axis
    pitch := α, pitch_ne := hα }
  let Z : OriginalSmoothHelicoid := {
    carrier := PuncturedPeriodTorus certifiedPeriodPair, charts := puncturedPeriodTorusChartedSpace certifiedPeriodPair
    manifold := IsManifold.of_le (n := ω) (by simp), modelTorus := certifiedPeriodPair
    topologicalType := Homeomorph.refl _, position := X, closedEmbedding := he
    smooth := H.analytic.of_le le_top, immersion := fun q => (H.immersion q).mfderiv_injective
    minimal := H.minimal, axes := axes }
  have hzero : (![0,0,0] : Fin 3 → ℝ) = 0 := by ext j; fin_cases j <;> rfl
  have hN : axisSpatialNormalization hα ![0,0,0] ∘ X = certifiedNormalizedTorusImmersion := by
    funext q
    rw [Function.comp_apply,certifiedNormalizedTorusImmersion_eq_fixed_similarity hα q,hzero]
    simp only [axisSpatialNormalization_apply,map_zero,sub_zero,X,centeredActualTorusImmersion,map_sub]
    rfl
  let s : OriginalHelicoidRepresentative := { Z with
    graphEnd := by
      change HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα ![0,0,0] ∘ X)
      rw [hN]
      exact certifiedTorusImmersion_C1_helicoid_end }
  exact ⟨s,rfl,rfl,rfl,rfl⟩

/-- With the geometric reduction from arbitrary surfaces, the published
existence input is equivalent to a compact injectivity test on the single
certified torus. The implication from this test to existence uses no external
geometry or existence statement. -/
theorem certified_compact_core_iff_original_exists (bbc : PublishedOneHandleEndTheorem)
    (poincare : SimplyConnectedNoncompactUniformization.{0}) (hw : GeometricTwoAxisIntersectionTheorem) :
    ∃ K : Set (PuncturedPeriodTorus certifiedPeriodPair), IsCompact K ∧
      immersionDoublePoints certifiedTorusImmersion ⊆ K ×ˢ K ∧
      (Nonempty OriginalPositionallyAsymptoticHelicoid ↔ InjOn certifiedTorusImmersion K) := by
  obtain ⟨_,K,hK,hs,he⟩ := certified_compact_embedding_criterion
  refine ⟨K,hK,hs,?_,?_⟩
  · intro existsSurface
    have result := theorem_1_1_from_published_geometric_inputs bbc poincare hw existsSurface
    exact he.mp result.2.2.1
  · intro h
    obtain ⟨s,_⟩ := certified_original_representative_of_injective (he.mpr h).injective
    exact ⟨s.toPositional⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_original_representative_of_injective
#print axioms TwoAxisHelicoid.certified_compact_core_iff_original_exists
