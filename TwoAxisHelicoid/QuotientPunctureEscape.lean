import TwoAxisHelicoid.CompactPunctureProper
import TwoAxisHelicoid.PeriodTorusDescent

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

theorem open_map_puncture_escape {M : Type*} [TopologicalSpace M]
    {p : M} {π : ℂ → M} (hπ : IsOpenMap π) (hπ0 : π 0 = p)
    {X : M → Fin 3 → ℝ}
    (hX : Tendsto (X ∘ π) (𝓝[≠] (0 : ℂ)) (cobounded (Fin 3 → ℝ))) :
    Tendsto X (𝓝[≠] p) (cobounded (Fin 3 → ℝ)) := by
  apply tendsto_norm_atTop_iff_cobounded.mp
  apply tendsto_atTop.mpr
  intro B
  have hB : ∀ᶠ z in 𝓝[≠] (0 : ℂ), B ≤ ‖X (π z)‖ :=
    (tendsto_norm_atTop_iff_cobounded.mpr hX).eventually_ge_atTop B
  simp only [nhdsWithin,eventually_inf_principal] at hB
  obtain ⟨U,hU,hUopen,hU0⟩ := mem_nhds_iff.mp hB
  have hv : π '' U ∈ 𝓝 p := (hπ U hUopen).mem_nhds ⟨0,hU0,hπ0⟩
  filter_upwards [nhdsWithin_le_nhds hv,self_mem_nhdsWithin] with q hq hqn
  obtain ⟨z,hz,rfl⟩ := hq
  apply hU hz
  change z ≠ 0
  intro hz0
  apply hqn
  change π z = p
  simpa only [hz0] using hπ0

theorem periodTorusLift_puncture_escape (L : PeriodPair) {F : ℂ → Fin 3 → ℝ}
    (hp : ∀ z ω, ω ∈ L.lattice → F (z+ω) = F z)
    (hF : Tendsto F (𝓝[≠] (0 : ℂ)) (cobounded (Fin 3 → ℝ))) :
    Tendsto (periodTorusLift L F hp) (𝓝[≠] 0) (cobounded (Fin 3 → ℝ)) := by
  apply open_map_puncture_escape (π := periodTorusProjection L)
    QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap
    ((periodTorusProjection_eq_zero L 0).mpr L.lattice.zero_mem)
  exact hF

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodTorusLift_puncture_escape
