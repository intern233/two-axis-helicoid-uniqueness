import TwoAxisHelicoid.HarmonicNullLift
import TwoAxisHelicoid.NullGaussIntegerReduction

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Reduction for an actual harmonic conformal immersion on the punctured
rhombic cover. Its meromorphic coefficients, nullity, regularity and both
reflection rules are consequences of the map. The two end principal parts
remain explicit hypotheses; this is not the original geometric theorem. -/
theorem harmonic_conformal_integer_data_reduction {t : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    {A κ : ℂ} (hA : A ≠ 0) {rh rg : ℂ → ℂ}
    (hrh : AnalyticAt ℂ rh 0) (hrg : AnalyticAt ℂ rg 0)
    (hheightEnd : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = A/z^2+rh z)
    (hgaussEnd : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = κ/z^2+rg z) :
    ∃ (a c : ℝ) (q : ℂ → Fin 3 → ℂ) (m : ℤ),
      a ∈ Ioo (0 : ℝ) 1 ∧ c ≠ 0 ∧ t < ellipticVerticalUpper ∧ a = verticalA t ∧
      (q = puncturedImmersionCoefficient (rhombicPeriodPair t ht) X ∨
        q = fun z => flipNullY (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) ∧
      (∀ z ∉ (rhombicPeriodPair t ht).lattice,
        q z 2 = I*c*((rhombicPeriodPair t ht).weierstrassP z-
          (rhombicPeriodPair t ht).weierstrassP a)) ∧
      ((∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss (q z) = thetaGauss t a m z) ∨
       (∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss (q z) = -thetaGauss t a m z)) := by
  apply regular_symmetric_null_data_integer_reduction ht
    (hX.null_differential (fun z hz => rhombic_conj_mem ht hz))
    (fun _ hz j => puncturedImmersionCoefficient_analyticAt hX hz j)
    (F := fun z => X z 2) ?_ ?_ hA hrh hrg hheightEnd hgaussEnd
  · intro z hz
    rw [puncturedImmersionCoefficient_eq hz]
    exact scalarComplexCoefficient_hasFDerivAt ((hX.harmonic z hz 2).1.differentiableAt two_ne_zero)
  · intro z hz ω hω
    exact congrFun (hX.periodic z hz ω hω) 2

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_conformal_integer_data_reduction
