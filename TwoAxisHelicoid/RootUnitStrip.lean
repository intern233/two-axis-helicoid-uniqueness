import TwoAxisHelicoid.RootEllipticPeriod
import TwoAxisHelicoid.WeierstrassRealMonotone

namespace TwoAxisHelicoid
open Set
attribute [local irreducible] thetaG thetaHorizontalPeriod

theorem root_abscissa_mem_unit {a : ℝ} (ha : a ∈ Ioo (rootALower:ℝ) rootAUpper) :
    a ∈ Ioo (0:ℝ) 1 := by
  have hl : (0:ℝ) < rootALower := by norm_num [rootALower]
  have hu : (rootAUpper:ℝ) < 1 := by norm_num [rootAUpper]
  exact ⟨hl.trans ha.1,ha.2.trans hu⟩

theorem root_thetaG_zero_eq_branch {t a : ℝ}
    (htl : (rootTLower:ℝ) ≤ t) (htu : t ≤ (rootTUpper:ℝ))
    (ha : a ∈ Ioo (0:ℝ) 1) (hz : thetaG t a = 0) : a = rootVerticalAReal t := by
  have ht86 : (43/50:ℝ) ≤ t :=
    (show (43/50:ℝ) ≤ (rootTLower:ℝ) by norm_num [rootTLower]).trans htl
  have hb := rootVerticalAReal_spec ⟨htl,htu⟩
  apply (thetaG_strictAnti_unit ht86).injOn ha (root_abscissa_mem_unit hb.1)
  change (thetaG t a).re = (thetaG t (rootVerticalAReal t)).re
  rw [hz,hb.2]

theorem existsUnique_root_vertical_unit {t : ℝ}
    (htl : (rootTLower:ℝ) ≤ t) (htu : t ≤ (rootTUpper:ℝ)) :
    ∃! a, a ∈ Ioo (0:ℝ) 1 ∧ thetaG t a = 0 := by
  have hb := rootVerticalAReal_spec ⟨htl,htu⟩
  exact ⟨rootVerticalAReal t,⟨root_abscissa_mem_unit hb.1,hb.2⟩,
    fun a ha => root_thetaG_zero_eq_branch htl htu ha.1 ha.2⟩

/-- The abscissa restriction in the local common-root theorem can be enlarged
to the entire geometric interval (0,1), while the height remains local. -/
theorem existsUnique_root_common_period_unit_strip :
    ∃! p : ℝ × ℝ, p.1 ∈ Ioo (rootTLower:ℝ) rootTUpper ∧
      p.2 ∈ Ioo (0:ℝ) 1 ∧ thetaG p.1 p.2 = 0 ∧ thetaHorizontalPeriod p.1 p.2 = 0 := by
  obtain ⟨p,hp,hu⟩ := existsUnique_root_common_period_zero
  refine ⟨p,⟨hp.1,root_abscissa_mem_unit hp.2.1,hp.2.2⟩,?_⟩
  intro q hq
  have he := root_thetaG_zero_eq_branch hq.1.1.le hq.1.2.le hq.2.1 hq.2.2.1
  have hb := (rootVerticalAReal_spec ⟨hq.1.1.le,hq.1.2.le⟩).1
  rw [← he] at hb
  exact hu q ⟨hq.1,hb,hq.2.2⟩

theorem root_elliptic_vertical_unit_agrees {t a : ℝ}
    (htl : (rootTLower:ℝ) ≤ t) (ha : a ∈ Ioo (0:ℝ) 1) :
    ellipticVerticalPeriod t a = thetaG t a := by
  have ht0 := root_t_positive htl
  have ht86 : (43/50:ℝ) ≤ t :=
    (show (43/50:ℝ) ≤ (rootTLower:ℝ) by norm_num [rootTLower]).trans htl
  simp only [ellipticVerticalPeriod,dite_eq_left ht0]
  exact (thetaG_eq_weierstrassP ht86 ht0 a
    (real_not_mem_rhombic_lattice ht86 ht0 ha.1 (by linarith [ha.2]))).symm

theorem existsUnique_root_elliptic_period_unit_strip :
    ∃! p : ℝ × ℝ, p.1 ∈ Ioo (rootTLower:ℝ) rootTUpper ∧
      p.2 ∈ Ioo (0:ℝ) 1 ∧ ellipticVerticalPeriod p.1 p.2 = 0 ∧
      sigmaHorizontalPeriod p.1 p.2 = 0 := by
  obtain ⟨p,hp,_⟩ := existsUnique_root_elliptic_period_zero
  refine ⟨p,⟨hp.1,root_abscissa_mem_unit hp.2.1,hp.2.2.1,hp.2.2.2.1⟩,?_⟩
  intro q hq
  have hG := (root_elliptic_vertical_unit_agrees hq.1.1.le hq.2.1).symm.trans hq.2.2.1
  have he := root_thetaG_zero_eq_branch hq.1.1.le hq.1.2.le hq.2.1 hG
  have hb := (rootVerticalAReal_spec ⟨hq.1.1.le,hq.1.2.le⟩).1
  rw [← he] at hb
  have hqe := root_elliptic_periods_agree hq.1.1.le hq.1.2.le hb.1.le hb.2.le
  have hpe := root_elliptic_periods_agree hp.1.1.le hp.1.2.le hp.2.1.1.le hp.2.1.2.le
  have hu := root_common_period_unique hq.1 hb hp.1 hp.2.1 hG
    (hqe.2.symm.trans hq.2.2.2) (hpe.1.symm.trans hp.2.2.1)
    (hpe.2.symm.trans hp.2.2.2.1)
  exact Prod.ext hu.1 hu.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.existsUnique_root_elliptic_period_unit_strip
