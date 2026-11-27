import TwoAxisHelicoid.VerticalBranchContinuity

namespace TwoAxisHelicoid
open Set Filter Complex
open scoped Topology
attribute [local irreducible] thetaJet thetaQuotient thetaG verticalA

theorem thetaG_strictAnti_to_one {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (fun x : ℝ => (thetaG t x).re) (Ioc (0:ℝ) 1) := by
  intro x hx y hy hxy
  change (thetaG t y).re < (thetaG t x).re
  rw [thetaG_eq_weierstrassP_of_pos ht ht x
    (real_not_mem_rhombic_lattice_of_pos ht hx.1 (by linarith [hx.2])),
    thetaG_eq_weierstrassP_of_pos ht ht y
    (real_not_mem_rhombic_lattice_of_pos ht hy.1 (by linarith [hy.2]))]
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re]
  have h := rhombic_weierstrassP_strictAnti_to_one ht hx hy hxy
  dsimp only at h
  linarith

theorem thetaG_vertical_upper_one_zero : thetaG ellipticVerticalUpper 1 = 0 := by
  apply Complex.ext
  · rw [thetaG_one_reciprocal_real ellipticVerticalUpper_pos]
    simp only [ellipticVerticalUpper,one_div_one_div,ellipticCriticalT_zero,neg_zero,zero_div,Complex.zero_re]
  · exact thetaG_real _ _

theorem verticalA_tendsto_one : Tendsto verticalA (𝓝[<] ellipticVerticalUpper) (𝓝 1) := by
  have hp : ∀ᶠ s in 𝓝[<] ellipticVerticalUpper, 0 < s :=
    (eventually_gt_nhds ellipticVerticalUpper_pos).filter_mono nhdsWithin_le_nhds
  have hu : ∀ᶠ s in 𝓝[<] ellipticVerticalUpper, s < ellipticVerticalUpper := self_mem_nhdsWithin
  have hdom := hp.and hu
  apply tendsto_order.mpr
  constructor
  · intro l hl
    obtain ⟨b,hb0,hb1⟩ := exists_between (max_lt hl (by norm_num : (0:ℝ) < 1))
    have hbpos : 0 < b := (le_max_right l 0).trans_lt hb0
    have hbl : l < b := (le_max_left l 0).trans_lt hb0
    have hgt : 0 < (thetaG ellipticVerticalUpper b).re := by
      have h := thetaG_strictAnti_to_one ellipticVerticalUpper_pos ⟨hbpos,hb1.le⟩
        (by norm_num : (1:ℝ) ∈ Ioc 0 1) hb1
      simpa only [thetaG_vertical_upper_one_zero,Complex.zero_re] using h
    have he : ∀ᶠ s in 𝓝[<] ellipticVerticalUpper, 0 < (thetaG s b).re :=
      (((thetaG_real_t_hasDerivAt ellipticVerticalUpper_pos hbpos (by linarith)).continuousAt).eventually
        (eventually_gt_nhds hgt)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hdom,he] with s hs hsg
    have hsa := verticalA_spec hs
    have hsz : (thetaG s (verticalA s)).re = 0 := by rw [hsa.2]; rfl
    have hba : b < verticalA s := by
      by_contra hn
      have hm := (thetaG_strictAnti_unit_of_pos hs.1).antitoneOn hsa.1 ⟨hbpos,hb1⟩ (le_of_not_gt hn)
      change (thetaG s b).re ≤ (thetaG s (verticalA s)).re at hm
      linarith
    exact hbl.trans hba
  · intro u hu1
    filter_upwards [hdom] with s hs
    exact (verticalA_spec hs).1.2.trans hu1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.verticalA_tendsto_one
