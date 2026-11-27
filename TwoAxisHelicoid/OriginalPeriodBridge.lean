import TwoAxisHelicoid.OriginalSlopingPeriod
import TwoAxisHelicoid.FullPeriodRoot
import TwoAxisHelicoid.FullPeriodAnalytic

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaA thetaSigmaKernel actualPeriodAlong

noncomputable def originalSigmaPeriod (t a : ℝ) : ℂ :=
  ((1-I*t)/2)*(∫ s : ℝ in (-1)..1, thetaSigmaKernel t a (originalPeriodPath t s))

theorem originalSigmaPeriod_eq_theta {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0:ℝ) 2) :
    originalSigmaPeriod t a = originalSlopingPeriod t a := by
  unfold originalSigmaPeriod originalSlopingPeriod
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  apply thetaSigmaKernel_eq_thetaA_of_pos ht ht
  · exact real_not_mem_rhombic_lattice_of_pos ht ha.1 ha.2
  · exact rhombic_open_rectangle_not_mem ht (originalPeriodPath_mem_rectangle ht
      (by simpa only [uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] using hs))

theorem originalSigmaPeriod_re_eq_horizontal {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0:ℝ) 2) :
    (originalSigmaPeriod t a).re = thetaHorizontalPeriod t a := by
  rw [originalSigmaPeriod_eq_theta ht ha,originalSlopingPeriod_re_eq_horizontal ht a]

noncomputable def originalPeriodAlong (t : ℝ) : ℝ :=
  (originalSigmaPeriod t (verticalA t)).re

theorem originalPeriodAlong_eq_actual {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    originalPeriodAlong t = actualPeriodAlong t := by
  have ha := (verticalA_spec ht).1
  unfold originalPeriodAlong actualPeriodAlong
  exact originalSigmaPeriod_re_eq_horizontal ht.1 ⟨ha.1,by linarith [ha.2]⟩

theorem originalPeriodAlong_eventuallyEq_actual {t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    originalPeriodAlong =ᶠ[𝓝 t] actualPeriodAlong := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact originalPeriodAlong_eq_actual hs

theorem originalPeriodAlong_analyticAt {t : ℝ} (ht : t ∈ Ioo (0:ℝ) ellipticVerticalUpper) :
    AnalyticAt ℝ originalPeriodAlong t :=
  (actualPeriodAlong_analyticAt ht).congr (originalPeriodAlong_eventuallyEq_actual ht).symm

theorem originalPeriodAlong_deriv_lt_neg_eight {t : ℝ}
    (ht : t ∈ Ioo (rootTLower:ℝ) rootTUpper) : deriv originalPeriodAlong t < -8 := by
  rw [(originalPeriodAlong_eventuallyEq_actual (root_height_in_full_domain ⟨ht.1.le,ht.2.le⟩)).deriv_eq]
  exact actualPeriodAlong_deriv_lt_neg_eight ht

theorem existsUnique_originalSigmaPeriod_root_locally :
    ∃! p : ℝ × ℝ, p.1 ∈ Ioo (rootTLower:ℝ) rootTUpper ∧
      p.2 ∈ Ioo (0:ℝ) 1 ∧ ellipticVerticalPeriod p.1 p.2 = 0 ∧
      (originalSigmaPeriod p.1 p.2).re = 0 := by
  have he {t a : ℝ} (ht : t ∈ Ioo (rootTLower:ℝ) rootTUpper) (ha : a ∈ Ioo (0:ℝ) 1) :
      ellipticVerticalPeriod t a = thetaG t a ∧
      (originalSigmaPeriod t a).re = thetaHorizontalPeriod t a :=
    ⟨root_elliptic_vertical_unit_agrees ht.1.le ha,
      originalSigmaPeriod_re_eq_horizontal (root_t_positive ht.1.le) ⟨ha.1,by linarith [ha.2]⟩⟩
  obtain ⟨p,hp,hu⟩ := existsUnique_root_common_period_unit_strip
  have hpe := he hp.1 hp.2.1
  refine ⟨p,⟨hp.1,hp.2.1,hpe.1.trans hp.2.2.1,hpe.2.trans hp.2.2.2⟩,?_⟩
  intro q hq
  have hqe := he hq.1 hq.2.1
  exact hu q ⟨hq.1,hq.2.1,hqe.1.symm.trans hq.2.2.1,hqe.2.symm.trans hq.2.2.2⟩

theorem exists_originalPeriodAlong_certified_simple_zero :
    ∃ t : ℝ, t ∈ Ioo (0:ℝ) ellipticVerticalUpper ∧
      t ∈ Ioo (rootTLower:ℝ) rootTUpper ∧
      verticalA t ∈ Ioo (rootALower:ℝ) rootAUpper ∧
      originalPeriodAlong t = 0 ∧ deriv originalPeriodAlong t < -8 := by
  obtain ⟨t,ht,hl,ha,hz,_⟩ := exists_actualPeriodAlong_certified_simple_zero
  exact ⟨t,ht,hl,ha,(originalPeriodAlong_eq_actual ht).trans hz,
    originalPeriodAlong_deriv_lt_neg_eight hl⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.existsUnique_originalSigmaPeriod_root_locally
#print axioms TwoAxisHelicoid.exists_originalPeriodAlong_certified_simple_zero
