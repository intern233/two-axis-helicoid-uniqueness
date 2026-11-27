import TwoAxisHelicoid.RootDerivativeData
import TwoAxisHelicoid.RootVerticalContinuity

namespace TwoAxisHelicoid
open Set
attribute [local irreducible] thetaG thetaJet thetaQuotient

theorem root_vertical_t_hasDerivAt {t a : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ))
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    HasDerivAt (fun s => (thetaG s a).re) (thetaGt t a).re t := by
  have h := thetaG_parameter_hasDerivAt (root_t_positive htl) a
    (root_vertical_denominator htl htu hal hau)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

theorem root_vertical_t_strictMono {a : ℝ}
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    StrictMonoOn (fun t => (thetaG t a).re) (Icc (rootTLower : ℝ) rootTUpper) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun t ht => (root_vertical_t_hasDerivAt ht.1 ht.2 hal hau).continuousAt.continuousWithinAt)
  intro t ht
  have hc := interior_subset ht
  rw [(root_vertical_t_hasDerivAt hc.1 hc.2 hal hau).deriv]
  have he := rootDerivativeParameters.sound rootDerivativeParameters_valid hc.1 hc.2 hal hau
  exact lt_of_lt_of_le (by norm_num) he.gt_lower

theorem rootVerticalA_strictMono : StrictMono rootVerticalA := by
  intro s t hst
  have ha := rootVerticalA_spec s
  have hb := rootVerticalA_spec t
  have hg := root_vertical_t_strictMono ha.1.1.le ha.1.2.le s.property t.property hst
  have hs0 : (thetaG s (rootVerticalA s)).re = 0 := by rw [ha.2]; rfl
  have ht0 : (thetaG t (rootVerticalA t)).re = 0 := by rw [hb.2]; rfl
  apply lt_of_not_ge
  intro h
  have hanti := (root_vertical_strictAnti t.property.1 t.property.2).antitoneOn
    (rootVerticalA t).property (rootVerticalA s).property h
  linarith

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.rootVerticalA_strictMono
