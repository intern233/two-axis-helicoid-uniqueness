import TwoAxisHelicoid.HelicoidalC1Similarity

namespace TwoAxisHelicoid
open Complex Set

/-- The actual closed punctured-torus immersion has a full C¹ helicoidal
end, up to a fixed spatial similarity of positive scale. -/
theorem actualTorusImmersion_hasHelicoidalC1End {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hG : thetaG t a = 0)
    (hH : thetaHorizontalPeriod t a = 0) :
    HasHelicoidalC1End (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      actualTorusImmersion ht ha hc hG hH q.1) := by
  let X := actualGlobalImmersion t a c ht
  let α : ℝ := 2*(a-1)/c
  have hα : α ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (ne_of_lt ha.2))) hc
  have hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht := fun z hz =>
    ((actual_global_conformal_harmonic_immersion ht ha hc hG hH).2.2.2 z hz).1
  have hp := actualGlobalImmersion_add_lattice ht ha hc hG hH
  have hend := actual_periodic_primitive_torus_C1_helicoid_end ht ha hc hX hp
  refine ⟨axisSpatialNormalization hα (X 1),|α|,abs_pos.mpr hα,?_,?_⟩
  · intro v w
    simpa only [sq_abs] using axisSpatialNormalization_squared_displacement hα (X 1) v w
  · have he : (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) => coordinateToTube
        (axisNormalizedTorusPrimitive (rhombicPeriodPair t ht) α X hp q.1)) =
        coordinateToTube ∘ axisSpatialNormalization hα (X 1) ∘
          (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
            actualTorusImmersion ht ha hc hG hH q.1) := by
      funext q
      rw [axisNormalizedTorusPrimitive_eq_space_map _ hα]
      rfl
    rw [← he]
    exact hend

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualTorusImmersion_hasHelicoidalC1End
