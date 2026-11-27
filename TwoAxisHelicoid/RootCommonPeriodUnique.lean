import TwoAxisHelicoid.RootCommonPeriod
import TwoAxisHelicoid.RootPeriodMonotonicity

namespace TwoAxisHelicoid
open Set

theorem root_common_period_unique {t a s b : ℝ}
    (ht : t ∈ Ioo (rootTLower : ℝ) rootTUpper) (ha : a ∈ Ioo (rootALower : ℝ) rootAUpper)
    (hs : s ∈ Ioo (rootTLower : ℝ) rootTUpper) (hb : b ∈ Ioo (rootALower : ℝ) rootAUpper)
    (hG : thetaG t a = 0) (hH : thetaHorizontalPeriod t a = 0)
    (hG' : thetaG s b = 0) (hH' : thetaHorizontalPeriod s b = 0) : t = s ∧ a = b := by
  let tt : RootHeight := ⟨t,ht.1.le,ht.2.le⟩
  let ss : RootHeight := ⟨s,hs.1.le,hs.2.le⟩
  have hat : a = (rootVerticalA tt : ℝ) :=
    (existsUnique_root_vertical_zero ht.1.le ht.2.le).unique ⟨ha,hG⟩ (rootVerticalA_spec tt)
  have hbs : b = (rootVerticalA ss : ℝ) :=
    (existsUnique_root_vertical_zero hs.1.le hs.2.le).unique ⟨hb,hG'⟩ (rootVerticalA_spec ss)
  have he : tt = ss := root_branch_period_strictAnti.injective (by
    change thetaHorizontalPeriod t (rootVerticalA tt) = thetaHorizontalPeriod s (rootVerticalA ss)
    rw [← hat, ← hbs, hH, hH'])
  exact ⟨congrArg Subtype.val he, by rw [hat,hbs,he]⟩

/-- Local existence and uniqueness for the two explicitly defined theta period
functions. Global period uniqueness and geometric classification are separate obligations. -/
theorem existsUnique_root_common_period_zero :
    ∃! p : ℝ × ℝ, p.1 ∈ Ioo (rootTLower : ℝ) rootTUpper ∧
      p.2 ∈ Ioo (rootALower : ℝ) rootAUpper ∧ thetaG p.1 p.2 = 0 ∧ thetaHorizontalPeriod p.1 p.2 = 0 := by
  obtain ⟨t,a,ht,ha,hG,hH⟩ := exists_root_common_period_zero
  refine ⟨(t,a),⟨ht,ha,hG,hH⟩,?_⟩
  intro p hp
  have h := root_common_period_unique hp.1 hp.2.1 ht ha hp.2.2.1 hp.2.2.2 hG hH
  exact Prod.ext h.1 h.2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.existsUnique_root_common_period_zero
