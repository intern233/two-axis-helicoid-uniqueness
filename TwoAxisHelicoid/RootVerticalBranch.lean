import TwoAxisHelicoid.RootVerticalLower
import TwoAxisHelicoid.RootVerticalUpper
import TwoAxisHelicoid.RootVerticalRegular
import TwoAxisHelicoid.ThetaSymmetry
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace TwoAxisHelicoid
open Set

theorem root_t_positive {t : ℝ} (ht : (rootTLower : ℝ) ≤ t) : 0 < t := by
  have hp : (0 : ℝ) < (rootTLower : ℝ) := by norm_num [rootTLower]
  exact hp.trans_le ht

theorem root_vertical_real_hasDerivAt {t a : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    HasDerivAt (fun b => (thetaG t b).re) (thetaGa t a).re a := by
  have h := thetaG_a_hasDerivAt (root_t_positive htl) a
    (root_vertical_denominator htl htu hal hau)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt a h

theorem root_vertical_continuous {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) :
    ContinuousOn (fun a => (thetaG t a).re) (Icc (rootALower : ℝ) rootAUpper) := by
  intro a ha
  exact (root_vertical_real_hasDerivAt htl htu ha.1 ha.2).continuousAt.continuousWithinAt

theorem root_vertical_strictAnti {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) :
    StrictAntiOn (fun a => (thetaG t a).re) (Icc (rootALower : ℝ) rootAUpper) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (root_vertical_continuous htl htu)
  intro a ha
  have hc := interior_subset ha
  rw [(root_vertical_real_hasDerivAt htl htu hc.1 hc.2).deriv]
  exact root_vertical_derivative_negative htl htu hc.1 hc.2

/-- The true theta vertical equation has a unique solution in the certified root box,
for every real height in the certified height interval. No enclosure is assumed. -/
theorem existsUnique_root_vertical_zero {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) :
    ∃! a, a ∈ Ioo (rootALower : ℝ) rootAUpper ∧ thetaG t a = 0 := by
  have hp := root_vertical_lower_positive htl htu
  have hn := root_vertical_upper_negative htl htu
  obtain ⟨a, ha, hz⟩ := intermediate_value_Icc'
    (by norm_num [rootALower, rootAUpper] : (rootALower : ℝ) ≤ rootAUpper)
    (root_vertical_continuous htl htu) ⟨hn.le, hp.le⟩
  dsimp only at hz
  have hai : a ∈ Ioo (rootALower : ℝ) rootAUpper := by
    constructor
    · refine lt_of_le_of_ne ha.1 ?_
      intro he
      rw [he, hz] at hp
      exact lt_irrefl _ hp
    · refine lt_of_le_of_ne ha.2 ?_
      intro he
      rw [← he, hz] at hn
      exact lt_irrefl _ hn
  have hzero : thetaG t a = 0 := by
    apply Complex.ext
    · exact hz
    · exact thetaG_real t a
  refine ⟨a, ⟨hai, hzero⟩, ?_⟩
  intro b hb
  apply (root_vertical_strictAnti htl htu).injOn ⟨hb.1.1.le, hb.1.2.le⟩ ha
  change (thetaG t b).re = (thetaG t a).re
  rw [hb.2, hzero]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.existsUnique_root_vertical_zero
