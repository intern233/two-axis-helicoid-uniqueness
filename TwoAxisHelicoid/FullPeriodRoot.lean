import TwoAxisHelicoid.FullPeriodBranch
import TwoAxisHelicoid.RootUnitStrip
import TwoAxisHelicoid.RootStrongDerivative

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology
attribute [local irreducible] thetaG thetaHorizontalPeriod

theorem root_height_in_full_domain {t : ℝ} (ht : t ∈ Icc (rootTLower:ℝ) rootTUpper) :
    t ∈ Ioo (0:ℝ) ellipticVerticalUpper := by
  refine ⟨root_t_positive ht.1,?_⟩
  have hu : (rootTUpper:ℝ) < 100000000/70945980 := by norm_num [rootTUpper]
  exact ht.2.trans_lt (hu.trans ellipticVerticalUpper_location.1)

theorem verticalA_eq_root_branch {t : ℝ} (ht : t ∈ Icc (rootTLower:ℝ) rootTUpper) :
    verticalA t = rootVerticalAReal t := by
  have ha := rootVerticalAReal_spec ht
  exact (verticalA_unique (root_height_in_full_domain ht) (root_abscissa_mem_unit ha.1) ha.2).symm

theorem actualPeriodAlong_eq_rootPeriodAlong {t : ℝ} (ht : t ∈ Icc (rootTLower:ℝ) rootTUpper) :
    actualPeriodAlong t = rootPeriodAlong t := by
  unfold actualPeriodAlong rootPeriodAlong
  rw [verticalA_eq_root_branch ht]

theorem actualPeriodAlong_deriv_lt_neg_eight {t : ℝ} (ht : t ∈ Ioo (rootTLower:ℝ) rootTUpper) :
    deriv actualPeriodAlong t < -8 := by
  have he : actualPeriodAlong =ᶠ[𝓝 t] rootPeriodAlong := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact actualPeriodAlong_eq_rootPeriodAlong hs
  rw [he.deriv_eq]
  exact rootPeriodAlong_deriv_lt_neg_eight ht

/-- The actual function on the full solvability domain has a certified simple
zero in the stated interval; uniqueness here is only inside that interval. -/
theorem existsUnique_actualPeriodAlong_root_locally :
    ∃! t : ℝ, t ∈ Ioo (rootTLower:ℝ) rootTUpper ∧ actualPeriodAlong t = 0 := by
  obtain ⟨p,hp,hu⟩ := existsUnique_root_common_period_unit_strip
  have hpt : p.1 ∈ Icc (rootTLower:ℝ) rootTUpper := ⟨hp.1.1.le,hp.1.2.le⟩
  have hpa : p.2 = verticalA p.1 := verticalA_unique (root_height_in_full_domain hpt) hp.2.1 hp.2.2.1
  have hpH : actualPeriodAlong p.1 = 0 := by
    unfold actualPeriodAlong
    rw [← hpa]
    exact hp.2.2.2
  refine ⟨p.1,⟨hp.1,hpH⟩,?_⟩
  intro t ht
  have hta := verticalA_spec (root_height_in_full_domain ⟨ht.1.1.le,ht.1.2.le⟩)
  have he := hu (t,verticalA t) ⟨ht.1,hta.1,hta.2,ht.2⟩
  exact congrArg Prod.fst he

theorem exists_actualPeriodAlong_certified_simple_zero :
    ∃ t : ℝ, t ∈ Ioo (0:ℝ) ellipticVerticalUpper ∧
      t ∈ Ioo (rootTLower:ℝ) rootTUpper ∧
      verticalA t ∈ Ioo (rootALower:ℝ) rootAUpper ∧
      actualPeriodAlong t = 0 ∧ deriv actualPeriodAlong t < -8 := by
  obtain ⟨t,ht,_⟩ := existsUnique_actualPeriodAlong_root_locally
  have htc : t ∈ Icc (rootTLower:ℝ) rootTUpper := ⟨ht.1.1.le,ht.1.2.le⟩
  refine ⟨t,root_height_in_full_domain htc,ht.1,?_,ht.2,actualPeriodAlong_deriv_lt_neg_eight ht.1⟩
  rw [verticalA_eq_root_branch htc]
  exact (rootVerticalAReal_spec htc).1

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.exists_actualPeriodAlong_certified_simple_zero
