import TwoAxisHelicoid.AxisSpatialNormalization
import TwoAxisHelicoid.ActualTorusProperness
import TwoAxisHelicoid.ActualTorusEndInjectivity

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

noncomputable def axisNormalizedTorusPrimitive (L : PeriodPair) (α : ℝ)
    (X : ℂ → Fin 3 → ℝ) (hp : ∀ z ω : ℂ, ω ∈ L.lattice → X (z+ω) = X z)
    (q : PeriodTorus L) : Fin 3 → ℝ :=
  verticalRotation I (α • (verticalRotation I (periodTorusLift L X hp q)-verticalRotation I (X 1)))

@[simp] theorem axisNormalizedTorusPrimitive_projection (L : PeriodPair) (α : ℝ)
    (X : ℂ → Fin 3 → ℝ) (hp : ∀ z ω : ℂ, ω ∈ L.lattice → X (z+ω) = X z) (z : ℂ) :
    axisNormalizedTorusPrimitive L α X hp (periodTorusProjection L z) =
      axisNormalizedPrimitive α X z := rfl

theorem axisNormalizedTorusPrimitive_eq_space_map (L : PeriodPair) {α : ℝ} (hα : α ≠ 0)
    (X : ℂ → Fin 3 → ℝ) (hp : ∀ z ω : ℂ, ω ∈ L.lattice → X (z+ω) = X z) :
    axisNormalizedTorusPrimitive L α X hp = axisSpatialNormalization hα (X 1) ∘ periodTorusLift L X hp := by
  funext q
  exact (axisSpatialNormalization_apply hα (X 1) (periodTorusLift L X hp q)).symm

theorem periodic_coordinate_primitive_torus_isProperMap
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z) :
    IsProperMap (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      periodTorusLift (rhombicPeriodPair t ht) X hp q.1) := by
  let L := rhombicPeriodPair t ht
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  apply compact_puncture_map_isProperMap
  · intro q hq
    obtain ⟨z,hz⟩ := Quotient.exists_rep q
    have hproj : periodTorusProjection L z = q := hz
    have hzn : z ∉ L.lattice := by
      intro h
      exact hq (hproj.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
    have hcont := periodTorusLift_continuousAt L X hp (hX z hzn).continuousAt
    simpa only [hproj] using hcont
  · exact periodTorusLift_puncture_escape L hp (actual_coordinate_primitive_end_escape ht ha hc hX)

theorem axisNormalizedTorusPrimitive_proper_and_end_injective
    {X : ℂ → Fin 3 → ℝ} {t a c α : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (hα : α ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z) :
    IsProperMap (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      axisNormalizedTorusPrimitive (rhombicPeriodPair t ht) α X hp q.1) ∧
      ∃ C : Set (PuncturedPeriodTorus (rhombicPeriodPair t ht)), IsCompact C ∧
        InjOn (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
          axisNormalizedTorusPrimitive (rhombicPeriodPair t ht) α X hp q.1) Cᶜ := by
  rw [axisNormalizedTorusPrimitive_eq_space_map _ hα]
  refine ⟨(axisSpatialNormalization hα (X 1)).isProperMap.comp
    (periodic_coordinate_primitive_torus_isProperMap ht ha hc hX hp),?_⟩
  obtain ⟨C,hC,hinj⟩ := actual_periodic_primitive_torus_end_injective ht ha hc hX hp
  refine ⟨C,hC,?_⟩
  intro q hq w hw he
  exact hinj hq hw ((axisSpatialNormalization hα (X 1)).injective he)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.axisNormalizedTorusPrimitive_proper_and_end_injective
