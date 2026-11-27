import TwoAxisHelicoid.ComplexEndOnePointCharts
import TwoAxisHelicoid.PuncturedDiskPolygon
import Mathlib.Topology.Compactness.LocallyCompact

namespace TwoAxisHelicoid
open Complex Set Filter Metric
open scoped Topology
set_option maxHeartbeats 1400000

/-- When a punctured-disk chart covers the complement of a compact
core, convergence of the forward coordinate to zero already forces
its inverse to leave every compact subset. A compact collar separates
the core from the one connected smaller punctured disk. -/
theorem punctured_disk_end_inverse_escapes {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    (e : OpenPartialHomeomorph M ℂ) {r : ℝ} (hr : 0 < r)
    (ht : e.target = ball (0:ℂ) r \ {0}) (hcore : IsCompact e.sourceᶜ)
    (hzero : Tendsto e (cocompact M) (𝓝 0)) : Tendsto e.symm (𝓝[≠] 0) (cocompact M) := by
  apply hasBasis_cocompact.tendsto_right_iff.mpr
  intro K hK
  obtain ⟨D,hD,hInt⟩ := exists_compact_superset (hK.union hcore)
  let B := D \ interior D
  have hB : IsCompact B := hD.inter_right isOpen_interior.isClosed_compl
  have hsrc : B ⊆ e.source := by
    intro x hx
    by_contra hh
    exact hx.2 (hInt (Or.inr hh))
  have hImage : IsCompact (e '' B) := hB.image_of_continuousOn (e.continuousOn.mono hsrc)
  have hImage₀ : (0 : ℂ) ∉ e '' B := by
    rintro ⟨x,hx,he⟩
    have hh := e.map_source (hsrc hx)
    rw [ht,he] at hh
    exact hh.2 rfl
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hImage.isClosed.isOpen_compl.mem_nhds hImage₀)
  let ρ := min δ r
  have hρ : 0 < ρ := lt_min hδ hr
  let U := ball (0:ℂ) ρ \ {0}
  have hU : U ⊆ e.target := by
    rw [ht]
    exact fun _ hw => ⟨ball_subset_ball (min_le_right δ r) hw.1,hw.2⟩
  let A := e.symm '' U
  have hc : IsPreconnected A := (complex_ball_diff_finite_isPreconnected 0 hρ (finite_singleton 0)).image _
    (e.symm.continuousOn.mono hU)
  have hA : A ⊆ interior D ∪ Dᶜ := by
    rintro _ ⟨w,hw,rfl⟩
    by_contra hbad
    have hB' : e.symm w ∈ B := ⟨by
      by_contra hn
      exact hbad (Or.inr hn),fun hi => hbad (Or.inl hi)⟩
    have hIm : w ∈ e '' B := ⟨e.symm w,hB',e.right_inv (hU hw)⟩
    exact hball (ball_subset_ball (min_le_left δ r) hw.1) hIm
  have hesc : ∃ x, x ∈ A ∧ x ∉ D := by
    have htail : ∀ᶠ x in cocompact M, x ∈ e.source := by
      change e.source ∈ cocompact M
      simpa only [compl_compl] using hcore.compl_mem_cocompact
    have hh : ∀ᶠ x in cocompact M, x ∈ e.source ∧ x ∉ D ∧ e x ∈ ball (0:ℂ) ρ := by
      filter_upwards [htail,hD.compl_mem_cocompact,hzero.eventually (ball_mem_nhds (0:ℂ) hρ)]
        with x hx hd hw
      exact ⟨hx,hd,hw⟩
    obtain ⟨x,hx,hd,hw⟩ := hh.exists
    have hn := e.map_source hx
    rw [ht] at hn
    exact ⟨x,⟨e x,⟨hw,hn.2⟩,e.left_inv hx⟩,hd⟩
  have hdis : Disjoint (interior D) Dᶜ := disjoint_compl_right.mono_left interior_subset
  rcases hc.subset_or_subset isOpen_interior hD.isClosed.isOpen_compl hdis hA with hpos | hneg
  · obtain ⟨x,hx,hn⟩ := hesc
    exact (hn (interior_subset (hpos hx))).elim
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) hρ),self_mem_nhdsWithin]
      with w hw hn
    exact fun hkw => (hneg (mem_image_of_mem _ (show w ∈ U from ⟨hw,hn⟩)))
      (interior_subset (hInt (Or.inl hkw)))

noncomputable def puncturedComplexEndOfChart {M : Type*} [TopologicalSpace M] [T2Space M]
    [WeaklyLocallyCompactSpace M] [NoncompactSpace M]
    (e : OpenPartialHomeomorph M ℂ) {r : ℝ} (hr : 0 < r)
    (ht : e.target = ball (0:ℂ) r \ {0}) (hcore : IsCompact e.sourceᶜ)
    (hzero : Tendsto e (cocompact M) (𝓝 0)) : PuncturedComplexEnd M where
  coord := e
  radius := r
  radius_pos := hr
  target_eq := ht
  compact_core := hcore
  to_zero := hzero
  from_zero := punctured_disk_end_inverse_escapes e hr ht hcore hzero

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_disk_end_inverse_escapes
