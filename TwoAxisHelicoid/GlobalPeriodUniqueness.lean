import TwoAxisHelicoid.PeriodConclusion
import TwoAxisHelicoid.LeftSignAll
import TwoAxisHelicoid.PositiveSignAll
import TwoAxisHelicoid.MiddleDerivativeAll
import TwoAxisHelicoid.NegativeSignAll
import TwoAxisHelicoid.RightSignAll
import TwoAxisHelicoid.VerticalZeroDomain
import TwoAxisHelicoid.OriginalHeightPeriod

/-! This file assembles the actual analytic period problem from the complete
sign certificates. It can be compiled only after every imported certificate and
its interval-cover theorem has passed. It does not prove surface uniqueness. -/
namespace TwoAxisHelicoid
open Set
attribute [local irreducible] actualPeriodAlong thetaG thetaHorizontalPeriod

/-- All five regions of the actual period function, with no remaining numeric
or sign hypothesis supplied by the caller. -/
theorem actualPeriodHypotheses : PeriodHypotheses actualPeriodAlong ellipticVerticalUpper where
  endpoint := (by norm_num : (7/5 : ℝ) < 100000000/70945980).trans
    ellipticVerticalUpper_location.1
  continuous := actualPeriodAlong_continuousOn.mono (fun _ ht => middle_height_in_full_domain ht)
  left := fun _ ht => actualPeriodAlong_positive_left ht.1 ht.2
  positive := fun _ ht => actualPeriodAlong_positive_compact ht.1 ht.2
  negative := fun _ ht => by simpa only [neg_div] using actualPeriodAlong_negative_compact ht.1 ht.2
  right := fun _ ht => by simpa only [neg_div] using actualPeriodAlong_right_certificate ht.1 ht.2
  derivative := fun _ ht => actualPeriodAlong_deriv_lt_neg_one_middle ht.1 ht.2

/-- The manuscript's global scalar uniqueness statement, on the entire
vertical solvability domain. -/
theorem existsUnique_actualPeriodAlong_zero_full_domain :
    ∃! t : ℝ, t ∈ Ioo (0 : ℝ) ellipticVerticalUpper ∧ actualPeriodAlong t = 0 :=
  existsUnique_period_zero_of_hypotheses actualPeriodHypotheses

theorem actualPeriodAlong_zero_global_location {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) (hz : actualPeriodAlong t = 0) :
    t ∈ Ioo (rootTLower : ℝ) rootTUpper ∧
      verticalA t ∈ Ioo (rootALower : ℝ) rootAUpper ∧ deriv actualPeriodAlong t < -8 := by
  have hm := zero_in_central_interval actualPeriodHypotheses ht hz
  exact actualPeriodAlong_middle_root_certified_location ⟨hm.1.le,hm.2.le⟩ hz

theorem actualPeriodAlong_zero_global_simple {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) (hz : actualPeriodAlong t = 0) :
    deriv actualPeriodAlong t ≠ 0 := by
  have hd := (actualPeriodAlong_zero_global_location ht hz).2.2
  linarith

/-- The full two-parameter period problem: all positive heights and the whole
geometric abscissa interval are considered. -/
theorem existsUnique_actual_common_period_full_domain :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 ∧
      thetaG p.1 p.2 = 0 ∧ thetaHorizontalPeriod p.1 p.2 = 0 := by
  obtain ⟨t,ht,hu⟩ := existsUnique_actualPeriodAlong_zero_full_domain
  have ha := verticalA_spec ht.1
  refine ⟨(t,verticalA t),⟨ht.1.1,ha.1,ha.2,?_⟩,?_⟩
  · simpa only [actualPeriodAlong] using ht.2
  · intro p hp
    obtain ⟨hdom,haeq⟩ := (thetaG_zero_iff_verticalA hp.1 hp.2.1).mp hp.2.2.1
    have hz : actualPeriodAlong p.1 = 0 := by
      unfold actualPeriodAlong
      rw [← haeq]
      exact hp.2.2.2
    have he := hu p.1 ⟨⟨hp.1,hdom⟩,hz⟩
    exact Prod.ext he (haeq.trans (congrArg verticalA he))

theorem existsUnique_originalPeriodAlong_zero_full_domain :
    ∃! t : ℝ, t ∈ Ioo (0 : ℝ) ellipticVerticalUpper ∧ originalPeriodAlong t = 0 := by
  obtain ⟨t,ht,hu⟩ := existsUnique_actualPeriodAlong_zero_full_domain
  refine ⟨t,⟨ht.1,?_⟩,?_⟩
  · rw [originalPeriodAlong_eq_actual ht.1]
    exact ht.2
  · intro s hs
    apply hu s
    refine ⟨hs.1,?_⟩
    rw [← originalPeriodAlong_eq_actual hs.1]
    exact hs.2

theorem originalPeriodAlong_zero_global_simple {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) ellipticVerticalUpper) (hz : originalPeriodAlong t = 0) :
    deriv originalPeriodAlong t < -8 := by
  have hza : actualPeriodAlong t = 0 := by
    rw [← originalPeriodAlong_eq_actual ht]
    exact hz
  rw [(originalPeriodAlong_eventuallyEq_actual ht).deriv_eq]
  exact (actualPeriodAlong_zero_global_location ht hza).2.2

/-- Global uniqueness of the actual closed coordinate data on the two primitive
lattice generators. Passing from an arbitrary embedded surface to these data
and identifying all geometric cycles remain separate geometric obligations. -/
theorem existsUnique_original_closed_data_global (c : ℝ) (hc : c ≠ 0) :
    ∃! p : ℝ × ℝ, ∃ ht : 0 < p.1, p.2 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ j : Fin 3, (originalCoordinatePeriod p.1 p.2 c ht j).re = 0 ∧
        (conjugateCoordinatePeriod p.1 p.2 c ht j).re = 0 := by
  obtain ⟨p,hp,hu⟩ := existsUnique_actual_common_period_full_domain
  have ha : p.2 ∈ Ioo (0 : ℝ) 2 := ⟨hp.2.1.1,by linarith [hp.2.1.2]⟩
  refine ⟨p,⟨hp.1,hp.2.1,(original_all_generators_close_iff hp.1 ha hc).mpr hp.2.2⟩,?_⟩
  rintro q ⟨hqt,haq,hclose⟩
  have haq2 : q.2 ∈ Ioo (0 : ℝ) 2 := ⟨haq.1,by linarith [haq.2]⟩
  exact hu q ⟨hqt,haq,(original_all_generators_close_iff hqt haq2 hc).mp hclose⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.existsUnique_actualPeriodAlong_zero_full_domain
#print axioms TwoAxisHelicoid.existsUnique_actual_common_period_full_domain
#print axioms TwoAxisHelicoid.existsUnique_original_closed_data_global
