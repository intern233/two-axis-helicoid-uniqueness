import TwoAxisHelicoid.RootCommonPeriodUnique
import TwoAxisHelicoid.RootSimplePeriod

namespace TwoAxisHelicoid
open Set

/-- The Jacobian determinant of the two actual theta periods has a strict sign
throughout the certified rectangle. -/
theorem root_period_jacobian_negative {t a : ℝ}
    (htl : (rootTLower:ℝ) ≤ t) (htu : t ≤ (rootTUpper:ℝ))
    (hal : (rootALower:ℝ) ≤ a) (hau : a ≤ (rootAUpper:ℝ)) :
    (thetaGt t a).re*rootPeriodDa t a-(thetaGa t a).re*rootPeriodDt t a < 0 := by
  have he := rootDerivativeParameters.sound rootDerivativeParameters_valid htl htu hal hau
  have ht : 0 < (thetaGt t a).re := lt_of_lt_of_le (by norm_num) he.gt_lower
  have ha := root_vertical_derivative_negative htl htu hal hau
  have hh := root_derivative_integrals_negative htl htu hal hau
  change rootPeriodDa t a < 0 ∧ rootPeriodDt t a < 0 at hh
  have hn := mul_neg_of_pos_of_neg ht hh.1
  have hp := mul_pos_of_neg_of_neg ha hh.2
  exact sub_neg.mpr (hn.trans hp)

/-- A unique simple common zero of the actual theta periods in the stated
local rectangle. This theorem does not assert uniqueness outside this box. -/
theorem existsUnique_root_certified_zero :
    ∃! p : ℝ × ℝ, p.1 ∈ Ioo (rootTLower:ℝ) rootTUpper ∧
      p.2 ∈ Ioo (rootALower:ℝ) rootAUpper ∧ thetaG p.1 p.2 = 0 ∧
      thetaHorizontalPeriod p.1 p.2 = 0 ∧ rootPeriodAlong p.1 = 0 ∧
      deriv rootPeriodAlong p.1 < 0 := by
  obtain ⟨p,hp,hu⟩ := existsUnique_root_common_period_zero
  have he : p.2 = rootVerticalAReal p.1 :=
    (existsUnique_root_vertical_zero hp.1.1.le hp.1.2.le).unique ⟨hp.2.1,hp.2.2.1⟩
      (rootVerticalAReal_spec ⟨hp.1.1.le,hp.1.2.le⟩)
  have hzero : rootPeriodAlong p.1 = 0 := by
    unfold rootPeriodAlong
    rw [← he]
    exact hp.2.2.2
  refine ⟨p,⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,hzero,rootPeriodAlong_deriv_neg hp.1⟩,?_⟩
  intro q hq
  exact hu q ⟨hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.1⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.existsUnique_root_certified_zero
