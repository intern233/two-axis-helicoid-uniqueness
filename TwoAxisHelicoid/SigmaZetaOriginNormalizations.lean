import TwoAxisHelicoid.SigmaAllIdentities
import TwoAxisHelicoid.OddLogarithmicDerivativeOrders

namespace TwoAxisHelicoid
open Complex Filter Set Asymptotics
open scoped Topology
attribute [local irreducible] thetaSigma thetaZeta

/-- The normalized sigma and zeta functions of the same rhombic lattice
have analytic remainders with the orders printed in section 2.1. -/
theorem sigma_zeta_origin_analytic_factors {t : ℝ} (ht : 0 < t) :
    ∃ A B : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧
      (∀ᶠ z in 𝓝 0, thetaSigma t z = z + z^5 * A z) ∧
      (∀ᶠ z in 𝓝[≠] 0, thetaZeta t z = z⁻¹ + z^3 * B z) := by
  apply odd_logarithmic_derivative_origin_factors (thetaSigma_analyticAt ht 0)
    (thetaSigma_neg t) (thetaSigma_hasDerivAt_zero_of_pos ht).deriv (thetaSigma_third_zero_of_pos ht)
  intro z regular
  exact (thetaSigma_hasDerivAt_zeta_of_pos ht ht (fun lattice =>
    regular ((thetaSigma_zero_iff_lattice_of_pos ht ht z).mpr lattice))).deriv

theorem sigma_zeta_origin_normalizations {t : ℝ} (ht : 0 < t) :
    ((fun z : ℂ => thetaSigma t z - z) =O[𝓝 0] (fun z => z^5)) ∧
    ((fun z : ℂ => thetaZeta t z - z⁻¹) =O[𝓝[≠] 0] (fun z => z^3)) := by
  exact odd_logarithmic_derivative_orders_of_divisor
    (P := fun z => z ∈ (rhombicPeriodPair t ht).lattice)
    (thetaSigma_analyticAt ht 0) (thetaSigma_neg t) (thetaSigma_hasDerivAt_zero_of_pos ht)
    (thetaSigma_third_zero_of_pos ht) (thetaSigma_zero_iff_lattice_of_pos ht ht)
    (fun hz => thetaSigma_hasDerivAt_zeta_of_pos ht ht hz)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.sigma_zeta_origin_analytic_factors
#print axioms TwoAxisHelicoid.sigma_zeta_origin_normalizations
