import TwoAxisHelicoid.EmbeddedPitchFamily
import TwoAxisHelicoid.HarmonicAxisIntersectionPoint
import TwoAxisHelicoid.ActualTorusC1HelicoidEnd
import TwoAxisHelicoid.ActualPrimitiveEndEscape

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Every representative admitted to the Appendix B compactness family
has both complete coordinate axes through the marked origin, closed
embedded image, and a C¹ helicoidal end at exactly unit pitch. The
normalization of its end fixes the origin and has scale one. -/
theorem embedded_pitch_family_unit_helicoid_geometry (W : PitchNormalizedBasicImmersion)
    (hW : W ∈ embeddedPitchFamily) :
    ∃ h : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair W.t W.ht) W.position,
      let F := harmonicTorusImmersion h
      let α := 2*(verticalA W.t-1)/W.c
      ∃ hα : α ≠ 0, |α| = 1 ∧ IsClosedEmbedding F ∧ F (rhombicAxisPoint W.ht) = 0 ∧
        (∀ x : ℝ, (![x,0,0] : Fin 3 → ℝ) ∈ range F) ∧ (∀ z : ℝ, (![0,0,z] : Fin 3 → ℝ) ∈ range F) ∧
        HasHelicoidC1End (coordinateToTube ∘ axisSpatialNormalization hα 0 ∘ F) := by
  obtain ⟨h,hi⟩ := hW
  let L := rhombicPeriodPair W.t W.ht
  let a := verticalA W.t
  let α := 2*(a-1)/W.c
  have ha : a ∈ Ioo (0:ℝ) 1 := (verticalA_spec ⟨W.ht,W.hT⟩).1
  have hc : W.c ≠ 0 := by
    intro hc
    have e := W.scale
    rw [hc,abs_zero] at e
    change (0:ℝ) = 2*(1-a) at e
    linarith [ha.2]
  have hα : α ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr ha.2.ne)) hc
  have hu : |α| = 1 := by
    rw [show α = 2*(a-1)/W.c from rfl,abs_div,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_neg (sub_neg.mpr ha.2),W.scale]
    change 2 * -(a-1)/(2*(1-a)) = 1
    rw [neg_sub,div_self (mul_ne_zero (by norm_num) (sub_pos.mpr ha.2).ne')]
  let B := punctureFilledMap L W.position
  have hB : HasTwoAxisHelicoidCoordinateDifferential B W.t a W.c W.ht :=
    fun z hz => (W.differential z hz).congr_of_eventuallyEq (punctureFilledMap_eventuallyEq hz)
  have hp := punctureFilledMap_periodic W.periodic
  have hEnd : HasHelicoidC1End (fun q : PuncturedPeriodTorus L => coordinateToTube (axisNormalizedTorusPrimitive L α B hp q.1)) :=
    actual_periodic_primitive_torus_C1_helicoid_end W.ht ha hc hB hp
  have h₁ : B 1 = 0 := (punctureFilledMap_eq (z := 1) (L := L)
    (by simpa using real_not_mem_rhombic_lattice_of_pos W.ht (by norm_num : (0:ℝ) < 1) (by norm_num))).trans
      (harmonic_axis_parameter_one W.ht h)
  have escape := actual_coordinate_primitive_end_escape W.ht ha hc W.differential
  obtain ⟨horiz,vert⟩ := harmonic_escaping_immersion_contains_axes W.ht h escape
  refine ⟨h,hα,hu,harmonicTorusImmersion_closedEmbedding_of_escape h hi escape
    (rhombic_puncture_eventually_off_lattice W.ht),harmonicTorus_axis_point W.ht h,?_,?_,?_⟩
  · intro x
    obtain ⟨z,hz,he⟩ := horiz x
    rw [harmonicTorusImmersion_range]
    exact ⟨z,hz,he⟩
  · intro x
    obtain ⟨z,hz,he⟩ := vert x
    rw [harmonicTorusImmersion_range]
    exact ⟨z,hz,he⟩
  · have he : (fun q : PuncturedPeriodTorus L => coordinateToTube (axisNormalizedTorusPrimitive L α B hp q.1)) =
        coordinateToTube ∘ axisSpatialNormalization hα 0 ∘ harmonicTorusImmersion h := by
      funext q
      rw [axisNormalizedTorusPrimitive_eq_space_map L hα,h₁]
      rfl
    exact he ▸ hEnd

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_pitch_family_unit_helicoid_geometry
