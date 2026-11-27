import TwoAxisHelicoid.PeriodicPunctureGeometry

namespace TwoAxisHelicoid
open Set Complex Metric Topology Bornology Filter
open scoped Topology

/-- Properness of the actual descended immersion forces spatial
escape near every lift of its puncture. The map on the cover is only
compared with the descended map at its regular parameters. -/
theorem proper_torus_cover_escapes_lattice {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {L : PeriodPair} {Y : PuncturedPeriodTorus L → E} {X : ℂ → E} (proper : IsProperMap Y)
    (lift : ∀ z (hz : z ∉ L.lattice), Y ⟨periodTorusProjection L z,fun e => hz ((periodTorusProjection_eq_zero L z).mp e)⟩=X z)
    {p : ℂ} (hp : p ∈ L.lattice) :
    Tendsto X (𝓝[(L.lattice : Set ℂ)ᶜ] p) (cobounded E) := by
  let : T1Space (PeriodTorus L) := QuotientAddGroup.t1Space_iff.mpr L.isClosed_lattice
  apply tendsto_norm_atTop_iff_cobounded.mp
  apply Filter.tendsto_atTop.mpr
  intro A
  let K := Y ⁻¹' closedBall (0:E) A
  let C := (Subtype.val : PuncturedPeriodTorus L → PeriodTorus L) '' K
  have compact : IsCompact C := (proper.isCompact_preimage (isCompact_closedBall _ _)).image continuous_subtype_val
  have zero : (0 : PeriodTorus L) ∉ C := by rintro ⟨q,_,e⟩; exact q.2 e
  have near : ∀ᶠ z in 𝓝 p, periodTorusProjection L z ∉ C := by
    have ht : Continuous (periodTorusProjection L) := QuotientAddGroup.continuous_mk
    have hnot : periodTorusProjection L p ∉ C := (periodTorusProjection_eq_zero L p).mpr hp ▸ zero
    exact ht.continuousAt (compact.isClosed.isOpen_compl.mem_nhds hnot)
  filter_upwards [self_mem_nhdsWithin,near.filter_mono nhdsWithin_le_nhds] with z hz hn
  by_contra! bound
  let q : PuncturedPeriodTorus L := ⟨periodTorusProjection L z,fun e => hz ((periodTorusProjection_eq_zero L z).mp e)⟩
  apply hn
  refine ⟨q,?_,rfl⟩
  change dist (Y q) 0≤A
  rw [show Y q=X z from lift z hz,dist_zero_right]
  exact bound.le

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.proper_torus_cover_escapes_lattice
