import TwoAxisHelicoid.MovingEllipticPeriod

namespace TwoAxisHelicoid
open Complex Set

theorem periodD_eq_weierstrass_derivatives {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 2) :
    periodD t a = (deriv (rhombicPeriodPair t ht).derivWeierstrassP (a : ℂ)).re/
      (2*((rhombicPeriodPair t ht).derivWeierstrassP a).re) := by
  unfold periodD
  rw [thetaLogFourth_eq_weierstrassP_second ht
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 ha.2),
    thetaGa_re_eq_wp_deriv ht ha.1 ha.2]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodD_eq_weierstrass_derivatives
