import TwoAxisHelicoid.ZetaPoleRegular
import TwoAxisHelicoid.WeierstrassOriginPrincipalParts

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology
attribute [local irreducible] thetaSigma thetaZeta

private theorem wp_origin_reg_decompose (L : PeriodPair) (z : ℂ) :
    L.weierstrassP z = z⁻¹^2 + L.weierstrassPExcept 0 z := by
  simpa [one_div,inv_pow,add_comm] using (L.weierstrassPExcept_add 0 z).symm

private theorem zeta_regular_derivative_germ {t : ℝ} (ht : 0<t) :
    zetaPoleRegular t 0 = 0 ∧ (deriv (zetaPoleRegular t) =ᶠ[𝓝 0]
      fun z => -(rhombicPeriodPair t ht).weierstrassPExcept 0 z) := by
  let L := rhombicPeriodPair t ht
  let R := zetaPoleRegular t
  have an : AnalyticAt ℂ R 0 := zetaPoleRegular_analyticAt ht (Or.inr rfl)
  have punctured : ∀ᶠ z in 𝓝[≠] (0:ℂ), z∉L.lattice := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin] with z isolated nz
    exact fun member => isolated ⟨member,nz⟩
  have odd : (fun z => R (-z)) =ᶠ[𝓝[≠] (0:ℂ)] fun z => -R z := by
    filter_upwards [punctured] with z nz
    have negz : -z∉L.lattice := fun h => nz (L.lattice.neg_mem_iff.mp h)
    have eq := thetaZeta_neg t z
    rw [thetaZeta_eq_inv_add_regular ht negz,thetaZeta_eq_inv_add_regular ht nz,inv_neg] at eq
    dsimp [R]
    linear_combination eq
  have atNeg : ContinuousAt R (-(0:ℂ)) := by simpa using an.continuousAt
  have oddAt := (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (atNeg.comp (continuous_neg.continuousAt : ContinuousAt (fun z : ℂ => -z) 0))
    an.continuousAt.neg).mp odd
  have zero : R 0 = 0 := by
    have e := oddAt.self_of_nhds
    change R (-(0:ℂ)) = -R 0 at e
    rw [neg_zero] at e
    linear_combination e / 2
  refine ⟨zero,?_⟩
  have derivative : deriv R =ᶠ[𝓝[≠] (0:ℂ)] fun z => -L.weierstrassPExcept 0 z := by
    filter_upwards [punctured] with z out
    have nz : z≠0 := by rintro rfl; exact out L.lattice.zero_mem
    have localEq : (thetaZeta t) =ᶠ[𝓝 z] fun w => w⁻¹ + R w := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds out] with w hw
      exact thetaZeta_eq_inv_add_regular ht hw
    have dr := (zetaPoleRegular_analyticAt ht (Or.inl out)).differentiableAt.hasDerivAt
    have eq := (thetaZeta_hasDerivAt_of_pos ht ht out).unique
      (((hasDerivAt_inv nz).add dr).congr_of_eventuallyEq localEq)
    change -L.weierstrassP z = -(z^2)⁻¹ + deriv R z at eq
    rw [wp_origin_reg_decompose,inv_pow] at eq
    linear_combination -eq
  exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE an.deriv.continuousAt
    (L.analyticAt_weierstrassPExcept 0).continuousAt.neg).mp derivative

/-- The Laurent coefficients used to compare constants in the heat equation
in Appendix A.1. Both errors have analytic factors for every positive height. -/
theorem elliptic_origin_laurent_factors {t : ℝ} (ht : 0<t) :
    let L := rhombicPeriodPair t ht
    ∃ A B : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ AnalyticAt ℂ B 0 ∧
      (∀ᶠ z in 𝓝 0, L.weierstrassP z = z⁻¹^2 + (L.g₂/20)*z^2 + z^4*A z) ∧
      (∀ᶠ z in 𝓝[≠] 0, thetaZeta t z = z⁻¹ - (L.g₂/60)*z^3 + z^5*B z) := by
  intro L
  obtain ⟨zero, derivative⟩ := zeta_regular_derivative_germ ht
  obtain ⟨A, B, ha, hb, wp, remainder⟩ := weierstrass_normalized_primitive_laurent L
    (zetaPoleRegular_analyticAt ht (Or.inr rfl)) zero derivative
  refine ⟨A, B, ha, hb, wp, ?_⟩
  filter_upwards [remainder.filter_mono nhdsWithin_le_nhds,
    mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hz isolated nonzero
  have off : z ∉ L.lattice := fun member => isolated ⟨member, nonzero⟩
  rw [thetaZeta_eq_inv_add_regular ht off, hz]
  ring

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.elliptic_origin_laurent_factors
