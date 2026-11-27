import TwoAxisHelicoid.VerticalRegularity

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
attribute [local irreducible] thetaJet thetaQuotient thetaG

noncomputable def verticalA (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper then
    ((existsUnique_thetaG_zero_full_domain ht.1).mpr ht.2).choose
  else 0

theorem verticalA_spec {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    verticalA t ∈ Ioo (0:ℝ) 1 ∧ thetaG t (verticalA t) = 0 := by
  simp only [verticalA,dite_eq_left ht]
  exact ((existsUnique_thetaG_zero_full_domain ht.1).mpr ht.2).choose_spec.1

theorem verticalA_unique {t a : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper)
    (ha : a ∈ Ioo (0:ℝ) 1) (hz : thetaG t a = 0) : a = verticalA t := by
  have h := (existsUnique_thetaG_zero_full_domain ht.1).mpr ht.2
  exact h.unique ⟨ha,hz⟩ (verticalA_spec ht)

theorem verticalA_continuousAt {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    ContinuousAt verticalA t := by
  have ha := verticalA_spec ht
  have hz : (thetaG t (verticalA t)).re = 0 := by rw [ha.2]; rfl
  have hdom : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0:ℝ) ellipticVerticalUpper := Ioo_mem_nhds ht.1 ht.2
  apply tendsto_order.mpr
  constructor
  · intro l hl
    obtain ⟨b,hb0,hba⟩ := exists_between (max_lt hl ha.1.1)
    have hbpos : 0 < b := (le_max_right l 0).trans_lt hb0
    have hbl : l < b := (le_max_left l 0).trans_lt hb0
    have hb1 : b < 1 := hba.trans ha.1.2
    have hp : 0 < (thetaG t b).re := by
      have h := thetaG_strictAnti_unit_of_pos ht.1 ⟨hbpos,hb1⟩ ha.1 hba
      simpa only [hz] using h
    have he : ∀ᶠ s in 𝓝 t, 0 < (thetaG s b).re :=
      ((thetaG_real_t_hasDerivAt ht.1 hbpos (by linarith)).continuousAt).eventually (eventually_gt_nhds hp)
    filter_upwards [hdom,he] with s hs hsp
    have hsa := verticalA_spec hs
    have hsz : (thetaG s (verticalA s)).re = 0 := by rw [hsa.2]; rfl
    have hba' : b < verticalA s := by
      by_contra hn
      have hm := (thetaG_strictAnti_unit_of_pos hs.1).antitoneOn hsa.1 ⟨hbpos,hb1⟩ (le_of_not_gt hn)
      change (thetaG s b).re ≤ (thetaG s (verticalA s)).re at hm
      linarith
    exact hbl.trans hba'
  · intro u hu
    obtain ⟨b,hab,hb1⟩ := exists_between (lt_min hu ha.1.2)
    have hbpos : 0 < b := ha.1.1.trans hab
    have hbu : b < u := hb1.trans_le (min_le_left u 1)
    have hbunit : b < 1 := hb1.trans_le (min_le_right u 1)
    have hn : (thetaG t b).re < 0 := by
      have h := thetaG_strictAnti_unit_of_pos ht.1 ha.1 ⟨hbpos,hbunit⟩ hab
      simpa only [hz] using h
    have he : ∀ᶠ s in 𝓝 t, (thetaG s b).re < 0 :=
      ((thetaG_real_t_hasDerivAt ht.1 hbpos (by linarith)).continuousAt).eventually (eventually_lt_nhds hn)
    filter_upwards [hdom,he] with s hs hsn
    have hsa := verticalA_spec hs
    have hsz : (thetaG s (verticalA s)).re = 0 := by rw [hsa.2]; rfl
    have hab' : verticalA s < b := by
      by_contra hp
      have hm := (thetaG_strictAnti_unit_of_pos hs.1).antitoneOn ⟨hbpos,hbunit⟩ hsa.1 (le_of_not_gt hp)
      change (thetaG s (verticalA s)).re ≤ (thetaG s b).re at hm
      linarith
    exact hab'.trans hbu

theorem verticalA_continuousOn : ContinuousOn verticalA (Ioo (0:ℝ) ellipticVerticalUpper) :=
  fun _ ht => (verticalA_continuousAt ht).continuousWithinAt

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.verticalA_continuousOn
