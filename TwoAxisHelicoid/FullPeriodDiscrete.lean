import TwoAxisHelicoid.FullPeriodAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology

theorem actualPeriodAlong_nonzero_somewhere :
    ∃ t ∈ Ioo (0:ℝ) ellipticVerticalUpper, actualPeriodAlong t ≠ 0 := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[<] ellipticVerticalUpper, 0 < t :=
    (eventually_gt_nhds ellipticVerticalUpper_pos).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ t : ℝ in 𝓝[<] ellipticVerticalUpper, t < ellipticVerticalUpper := self_mem_nhdsWithin
  obtain ⟨t,⟨ht0,htT⟩,hneg⟩ := ((hpos.and hlt).and actualPeriodAlong_eventually_negative_right).exists
  exact ⟨t,⟨ht0,htT⟩,hneg.ne⟩

theorem actualPeriodAlong_nonzero_codiscrete :
    ∀ᶠ t in codiscreteWithin (Ioo (0:ℝ) ellipticVerticalUpper), actualPeriodAlong t ≠ 0 := by
  rcases actualPeriodAlong_analyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected
      (convex_Ioo (0:ℝ) ellipticVerticalUpper).isPreconnected with hz | hn
  · obtain ⟨t,ht,hne⟩ := actualPeriodAlong_nonzero_somewhere
    exact False.elim (hne (hz ht))
  · exact hn

theorem actualPeriodAlong_zero_isolated {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    ∀ᶠ s in 𝓝[≠] t, actualPeriodAlong s ≠ 0 := by
  have h := eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp
    actualPeriodAlong_nonzero_codiscrete t ht
  filter_upwards [h,nhdsWithin_le_nhds (Ioo_mem_nhds ht.1 ht.2)] with s hs hsU
  exact hs hsU

theorem actualPeriodAlong_finite_zeros_on_compact {K : Set ℝ} (hK : IsCompact K)
    (hKU : K ⊆ Ioo (0:ℝ) ellipticVerticalUpper) :
    {t ∈ K | actualPeriodAlong t = 0}.Finite := by
  have hmem : {t | actualPeriodAlong t ≠ 0} ∈ codiscreteWithin K :=
    (Filter.codiscreteWithin_mono hKU) actualPeriodAlong_nonzero_codiscrete
  have he : K \ {t | actualPeriodAlong t ≠ 0} = {t ∈ K | actualPeriodAlong t = 0} := by
    ext t
    simp
  rw [← he]
  exact hK.finite_sdiff_of_mem_codiscreteWithin hmem

theorem actualPeriodAlong_negative_right_interval :
    ∃ b ∈ Ioo (0:ℝ) ellipticVerticalUpper,
      ∀ t ∈ Ioo b ellipticVerticalUpper, actualPeriodAlong t < 0 := by
  obtain ⟨b₀,hb₀,hbnd⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    actualPeriodAlong_eventually_negative_right
  have hb : max b₀ 0 < ellipticVerticalUpper := max_lt hb₀ ellipticVerticalUpper_pos
  obtain ⟨b,hbb,hbT⟩ := exists_between hb
  exact ⟨b,⟨(le_max_right b₀ 0).trans_lt hbb,hbT⟩,
    fun t ht => hbnd ⟨(le_max_left b₀ 0).trans_lt (hbb.trans ht.1),ht.2⟩⟩

/-- The actual period zeros can accumulate only at the small-height degeneration.
This does not exclude such an accumulation or prove global uniqueness. -/
theorem actualPeriodAlong_finite_zeros_above {ε : ℝ} (hε : 0 < ε) :
    {t : ℝ | ε ≤ t ∧ t < ellipticVerticalUpper ∧ actualPeriodAlong t = 0}.Finite := by
  obtain ⟨b,hb,hneg⟩ := actualPeriodAlong_negative_right_interval
  have hfin := actualPeriodAlong_finite_zeros_on_compact (K := Icc ε b) isCompact_Icc
    (fun _ ht => ⟨hε.trans_le ht.1,ht.2.trans_lt hb.2⟩)
  apply hfin.subset
  intro t ht
  refine ⟨⟨ht.1,?_⟩,ht.2.2⟩
  by_contra h
  have hn := hneg t ⟨lt_of_not_ge h,ht.2.1⟩
  rw [ht.2.2] at hn
  exact lt_irrefl _ hn

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.actualPeriodAlong_finite_zeros_on_compact
