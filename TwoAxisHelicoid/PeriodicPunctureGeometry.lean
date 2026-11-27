import TwoAxisHelicoid.CompactPunctureProperties
import TwoAxisHelicoid.QuotientPunctureEscape
import TwoAxisHelicoid.EmbeddedTorusAxesNormalization

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

theorem periodic_torus_isProperMap_of_puncture_escape (L : PeriodPair)
    {X : ℂ → Fin 3 → ℝ} (hp : ∀ z ω : ℂ, ω ∈ L.lattice → X (z+ω) = X z)
    (hX : ∀ z ∉ L.lattice, ContinuousAt X z)
    (hescape : Tendsto X (𝓝[≠] (0 : ℂ)) (cobounded (Fin 3 → ℝ))) :
    IsProperMap (fun q : PuncturedPeriodTorus L => periodTorusLift L X hp q.1) := by
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  apply compact_puncture_map_isProperMap
  · intro q hq
    obtain ⟨z,hz⟩ := Quotient.exists_rep q
    have hproj : periodTorusProjection L z = q := hz
    have hzn : z ∉ L.lattice := by
      intro h
      exact hq (hproj.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
    simpa only [hproj] using periodTorusLift_continuousAt L X hp (hX z hzn)
  · exact periodTorusLift_puncture_escape L hp hescape

theorem periodic_torus_end_injective_of_embedded_parameter (L : PeriodPair)
    {X : ℂ → Fin 3 → ℝ} (hp : ∀ z ω : ℂ, ω ∈ L.lattice → X (z+ω) = X z)
    {H K : ℂ → ℂ} {R : ℝ}
    (hH : Tendsto H (𝓝[≠] (0 : ℂ)) (cobounded ℂ))
    (hKL : ∀ᶠ z in 𝓝[≠] (0 : ℂ), K (H z) = z)
    (hEmb : Function.Injective (fun ξ : {ξ : ℂ // R ≤ ‖ξ‖} => X (K ξ.1))) :
    ∃ C : Set (PuncturedPeriodTorus L), IsCompact C ∧
      InjOn (fun q : PuncturedPeriodTorus L => periodTorusLift L X hp q.1) Cᶜ := by
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  have hprop : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ q : PuncturedPeriodTorus L,
      periodTorusProjection L z = q.1 →
      ∃ ξ : ℂ, R ≤ ‖ξ‖ ∧ periodTorusProjection L (K ξ) = q.1 := by
    filter_upwards [hKL,hH.eventually
      (tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop R))] with z hz hzn
    intro q hq
    exact ⟨H z,hzn,by rwa [hz]⟩
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
    (hEmb (a₁ := ⟨ξ,hξ⟩) (a₂ := ⟨η,hη⟩) hval)
  apply Subtype.ext
  rw [← hξq,← hηw,hξη]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodic_torus_isProperMap_of_puncture_escape
#print axioms TwoAxisHelicoid.periodic_torus_end_injective_of_embedded_parameter
