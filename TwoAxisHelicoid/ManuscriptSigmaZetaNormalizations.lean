import TwoAxisHelicoid.SigmaZetaOriginNormalizations

namespace TwoAxisHelicoid
open Asymptotics Complex Filter
open scoped Topology

/-- The four normalizations in §2.1, for the same lattice and the same two functions. -/
theorem manuscript_sigma_zeta_normalizations {t : ℝ} (ht : 0 < t) :
    (∀ z : ℂ, z ∉ (rhombicPeriodPair t ht).lattice →
      deriv (thetaZeta t) z = -(rhombicPeriodPair t ht).weierstrassP z ∧
      deriv (thetaSigma t) z / thetaSigma t z = thetaZeta t z) ∧
    ((fun z : ℂ => thetaSigma t z - z) =O[𝓝 0] (fun z => z ^ 5)) ∧
    ((fun z : ℂ => thetaZeta t z - z⁻¹) =O[𝓝[≠] 0] (fun z => z ^ 3)) := by
  refine ⟨?_, sigma_zeta_origin_normalizations ht⟩
  intro z hz
  have nonzero : thetaSigma t z ≠ 0 := fun h => hz ((thetaSigma_zero_iff_lattice_of_pos ht ht z).mp h)
  exact ⟨(thetaZeta_hasDerivAt_of_pos ht ht hz).deriv,
    (div_eq_iff nonzero).mpr (thetaSigma_hasDerivAt_zeta_of_pos ht ht hz).deriv⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_sigma_zeta_normalizations
