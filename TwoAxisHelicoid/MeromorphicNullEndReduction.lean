import TwoAxisHelicoid.EvenMeromorphicDoublePole
import TwoAxisHelicoid.NullGaussLogSymmetry
import TwoAxisHelicoid.HarmonicIntegerReduction

namespace TwoAxisHelicoid
open Complex Filter Set
open scoped Topology

/-- The two double-pole orders, in Mathlib's actual meromorphic sense,
suffice for the end expansions used by the reduction. Reflection removes
both residues; no Laurent coefficients or remainders are assumed. -/
theorem symmetric_null_meromorphic_end_principal_parts {L : PeriodPair}
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential L p)
    (ha : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hhOrder : meromorphicOrderAt (fun z => p z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt
      (fun z => deriv (fun w => nullGauss (p w)) z/nullGauss (p z)) 0 = (-2 : ℤ)) :
    ∃ (A κ : ℂ) (rh rg : ℂ → ℂ), A ≠ 0 ∧ κ ≠ 0 ∧
      AnalyticAt ℂ rh 0 ∧ AnalyticAt ℂ rg 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → p z 2 = A/z^2+rh z) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ),
        deriv (fun w => nullGauss (p w)) z/nullGauss (p z) = κ/z^2+rg z) := by
  have hhm : MeromorphicAt (fun z => p z 2) 0 :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hhOrder]; norm_num)
  have hgm : MeromorphicAt
      (fun z => deriv (fun w => nullGauss (p w)) z/nullGauss (p z)) 0 :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hgOrder]; norm_num)
  have hL : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      self_mem_nhdsWithin] with z hz hn hmem
    exact hz ⟨hmem,hn⟩
  have hhEven : ∀ᶠ z in 𝓝[≠] (0 : ℂ), p (-z) 2 = p z 2 := by
    filter_upwards [hL] with z hz
    simpa using congrFun (hp.neg z hz) 2
  have hhNZ : ∀ᶠ z in 𝓝[≠] (0 : ℂ), p z 2 ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hhm).mp (by rw [hhOrder]; simp)
  have hgEven : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv (fun w => nullGauss (p w)) (-z)/nullGauss (p (-z)) =
        deriv (fun w => nullGauss (p w)) z/nullGauss (p z) := by
    filter_upwards [hL,hhNZ] with z hz hn
    exact null_gauss_log_derivative_neg hp ha hz hn
  obtain ⟨A,rh,hA,hrh,hh⟩ := even_meromorphic_double_pole_principal_part hhm hhOrder hhEven
  obtain ⟨κ,rg,hκ,hrg,hg⟩ := even_meromorphic_double_pole_principal_part hgm hgOrder hgEven
  refine ⟨A,κ,rh,rg,hA,hκ,hrh,hrg,?_,hg⟩
  simpa only [eventually_nhdsWithin_iff,mem_compl_iff,mem_singleton_iff] using hh

/-- Actual harmonic conformal map plus the two meromorphic double-pole
orders implies the full integer data classification. Establishing those
orders and the conformal cover from the original surface remains geometric. -/
theorem harmonic_meromorphic_integer_data_reduction {t : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    ∃ (a c : ℝ) (q : ℂ → Fin 3 → ℂ) (m : ℤ),
      a ∈ Ioo (0 : ℝ) 1 ∧ c ≠ 0 ∧ t < ellipticVerticalUpper ∧ a = verticalA t ∧
      (q = puncturedImmersionCoefficient (rhombicPeriodPair t ht) X ∨
        q = fun z => flipNullY (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) ∧
      (∀ z ∉ (rhombicPeriodPair t ht).lattice,
        q z 2 = I*c*((rhombicPeriodPair t ht).weierstrassP z-
          (rhombicPeriodPair t ht).weierstrassP a)) ∧
      ((∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss (q z) = thetaGauss t a m z) ∨
       (∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss (q z) = -thetaGauss t a m z)) := by
  obtain ⟨A,κ,rh,rg,hA,_,hrh,hrg,hhe,hge⟩ :=
    symmetric_null_meromorphic_end_principal_parts
      (hX.null_differential (fun _ hz => rhombic_conj_mem ht hz))
      (fun _ hz j => puncturedImmersionCoefficient_analyticAt hX hz j) hhOrder hgOrder
  exact harmonic_conformal_integer_data_reduction ht hX hA hrh hrg hhe hge

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_meromorphic_integer_data_reduction
