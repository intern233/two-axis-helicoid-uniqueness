import TwoAxisHelicoid.RootDerivativeIntegral
import TwoAxisHelicoid.RootPeriodPartialDerivative
import TwoAxisHelicoid.RootRectanglePeriodContinuity
import TwoAxisHelicoid.RootVerticalIncreasing

namespace TwoAxisHelicoid
open Set
attribute [local irreducible] thetaHorizontalPeriod

theorem root_period_a_strictAnti {t : ℝ}
    (htl : (rootTLower : ℝ) ≤ t) (htu : t ≤ (rootTUpper : ℝ)) :
    StrictAntiOn (thetaHorizontalPeriod t) (Icc (rootALower : ℝ) rootAUpper) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (root_period_fixed_t_continuousOn htl htu)
  intro a ha
  have hai : a ∈ Ioo (rootALower : ℝ) rootAUpper := by simpa only [interior_Icc] using ha
  rw [(root_period_a_hasDerivAt htl htu hai).deriv]
  exact (root_derivative_integrals_negative htl htu hai.1.le hai.2.le).1

theorem root_period_t_strictAnti {a : ℝ}
    (hal : (rootALower : ℝ) ≤ a) (hau : a ≤ (rootAUpper : ℝ)) :
    StrictAntiOn (fun t => thetaHorizontalPeriod t a) (Icc (rootTLower : ℝ) rootTUpper) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (root_period_fixed_a_continuousOn hal hau)
  intro t ht
  have hti : t ∈ Ioo (rootTLower : ℝ) rootTUpper := by simpa only [interior_Icc] using ht
  rw [(root_period_t_hasDerivAt hti hal hau).deriv]
  exact (root_derivative_integrals_negative hti.1.le hti.2.le hal hau).2

theorem root_branch_period_strictAnti :
    StrictAnti (fun t : RootHeight => thetaHorizontalPeriod t (rootVerticalA t)) := by
  intro s t hst
  have htime := root_period_t_strictAnti (rootVerticalA t).property.1 (rootVerticalA t).property.2
    s.property t.property hst
  have hspace := (root_period_a_strictAnti s.property.1 s.property.2).antitoneOn
    (rootVerticalA s).property (rootVerticalA t).property (rootVerticalA_strictMono hst).le
  exact htime.trans_le hspace

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.root_branch_period_strictAnti
