import TwoAxisHelicoid.ActualEmbeddedEnd
import TwoAxisHelicoid.CompactPunctureProperties
import TwoAxisHelicoid.PeriodTorusDescent
import TwoAxisHelicoid.EmbeddedTorusAxesNormalization

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

/-- The embedded height subend descends to an injective complement of an
actual compact core in the punctured torus. This does not assert global
embeddedness of the whole immersion. -/
theorem actual_periodic_primitive_torus_end_injective
    {X : ℂ → Fin 3 → ℝ} {t a c : ℝ}
    (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z) :
    ∃ C : Set (PuncturedPeriodTorus (rhombicPeriodPair t ht)), IsCompact C ∧
      InjOn (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
        periodTorusLift (rhombicPeriodPair t ht) X hp q.1) Cᶜ := by
  let L := rhombicPeriodPair t ht
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  obtain ⟨K,R,_hKt,hKL,_hKR,hEmb⟩ := actual_primitive_has_embedded_height_end ht ha hc hX
  have hH := actualComplexHeight_tendsto (a := a) ht hc
  have hprop : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ q : PuncturedPeriodTorus L,
      periodTorusProjection L z = q.1 →
      ∃ ξ : ℂ, R ≤ ‖ξ‖ ∧ periodTorusProjection L (K ξ) = q.1 := by
    filter_upwards [hKL,hH.eventually
      (tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop R))] with z hz hzn
    intro q hq
    exact ⟨actualComplexHeight t a c ht z,hzn,by rwa [hz]⟩
  obtain ⟨C,hC,hCt⟩ := compact_puncture_projected_property
    (π := periodTorusProjection L) QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
    ((periodTorusProjection_eq_zero L 0).mpr L.lattice.zero_mem) hprop
  refine ⟨C,hC,?_⟩
  intro q hq w hw he
  obtain ⟨ξ,hξ,hξq⟩ := hCt q hq
  obtain ⟨η,hη,hηw⟩ := hCt w hw
  have hval : X (K ξ) = X (K η) := by
    change periodTorusLift L X hp (periodTorusProjection L (K ξ)) =
      periodTorusLift L X hp (periodTorusProjection L (K η))
    rwa [hξq,hηw]
  have hξη : ξ = η := congrArg Subtype.val
    (hEmb.injective (a₁ := ⟨ξ,hξ⟩) (a₂ := ⟨η,hη⟩) hval)
  apply Subtype.ext
  rw [← hξq,← hηw,hξη]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actual_periodic_primitive_torus_end_injective
