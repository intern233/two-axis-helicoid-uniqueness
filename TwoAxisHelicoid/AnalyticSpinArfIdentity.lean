import TwoAxisHelicoid.EmbeddedCapSpinParity
import TwoAxisHelicoid.HolomorphicSpinSectionBundle

namespace TwoAxisHelicoid
open Complex Set
open scoped ContDiff Manifold

variable {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : (C : ℂ)^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    {F : PeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ}
    {U : Set (PeriodTorus (rhombicPeriodPair t ht))} (hU : IsOpen U)
    (hfix : ∀ q ∈ U, F q = periodTorusLift (rhombicPeriodPair t ht) X hp q)
    (hcore : Subtype.val '' puncturedGeneratorCore (rhombicPeriodPair t ht) ⊆ U)

include ht ha hc m hC0 hC hX hp hh hg hU hfix hcore in
/-- The Arf invariant determined by the actual Euclidean generator frames
equals the parity of the ordinary mathlib analytic-sections space of
the holomorphic spin line, for every symplectic basis on the torus. -/
theorem ambient_cap_arf_eq_standard_analytic_spin_sections
    {v w : ZMod 2 × ZMod 2} (hvw : torusIntersectionModTwo v w = 1) :
    capAmbientSpinQuadratic (rhombicPeriodPair t ht) F v * capAmbientSpinQuadratic (rhombicPeriodPair t ht) F w =
      (Module.finrank ℂ (MultiplierAnalyticSection (rhombicPeriodPair t ht)
        (latticeSpinParity (rhombicPeriodPair t ht) m)) : ZMod 2) := by
  rw [cap_ambient_arf_eq_line_parity ht ha hc m hC0 hC hX hp hh hg hU hfix hcore hvw,
    (holomorphicMultiplierSectionBundleEquiv (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)).finrank_eq]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ambient_cap_arf_eq_standard_analytic_spin_sections
