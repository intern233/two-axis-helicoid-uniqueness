import TwoAxisHelicoid.NullGaussOrientation
import TwoAxisHelicoid.NullHeightReduction

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Complete integer Gauss classification derived from regular null
coefficients and their height form. The end's logarithmic principal part is
the remaining end-structure input; zero/pole data and orientation are proved. -/
theorem null_gauss_integer_reduction {t a : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    (hanalytic : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    {K : ℂ} (hK : K ≠ 0)
    (hheight : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    {κ : ℂ} {r : ℂ → ℂ} (hr : AnalyticAt ℂ r 0)
    (hend : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv (fun w => nullGauss (p w)) z/nullGauss (p z) = κ/z^2+r z) :
    ∃ (q : ℂ → Fin 3 → ℂ) (m : ℤ),
      (q = p ∨ q = fun z => flipNullY (p z)) ∧
      (κ = 2*((m : ℂ)-a) ∨ κ = -(2*((m : ℂ)-a))) ∧
      ((∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss (q z) = thetaGauss t a m z) ∨
       (∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss (q z) = -thetaGauss t a m z)) := by
  obtain ⟨q,hq,hg⟩ := exists_oriented_null_gauss_data ht ha hp hanalytic hK hheight
  rcases hq with hqp | hqf
  · rw [hqp] at hg
    obtain ⟨m,hm,hform⟩ := hg.integer_classification ht ha hr hend
    exact ⟨p,m,Or.inl rfl,Or.inl hm,hform⟩
  · rw [hqf] at hg
    have heflip : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
        deriv (fun w => nullGauss (flipNullY (p w))) z/nullGauss (flipNullY (p z)) =
          (-κ)/z^2+(-r z) := by
      filter_upwards [hend,latticePoleSet_punctured_avoids (rhombicPeriodPair t ht)
        (show ({0,(a : ℂ),-(a : ℂ)} : Set ℂ).Finite by simp) 0] with z he hz
      have hz' := (not_mem_gaussLogPoleSet (rhombicPeriodPair t ht) a z).mp hz
      rw [null_gauss_flip_log_derivative hp hz'.1 (hanalytic z hz'.1)
        (null_height_nonzero_away_pair ht ha hK hheight hz),he]
      ring
    obtain ⟨m,hm,hform⟩ := hg.integer_classification ht ha hr.neg heflip
    refine ⟨fun z => flipNullY (p z),m,Or.inr rfl,Or.inr ?_,hform⟩
    linear_combination -hm

/-- The marked analytic reduction now derives the normalized height zero,
vertical root branch and complete integer Gauss family from an actual
periodic height primitive, regular symmetric null coefficients and the two
specified end principal parts. -/
theorem regular_symmetric_null_data_integer_reduction {t : ℝ} (ht : 0 < t)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    (hanalytic : ∀ z ∉ (rhombicPeriodPair t ht).lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    {F : ℂ → ℝ}
    (hF : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      HasFDerivAt F (realCoefficientDerivative (p z 2)) z)
    (hFP : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      ∀ ω ∈ (rhombicPeriodPair t ht).lattice, F (z+ω) = F z)
    {A κ : ℂ} (hA : A ≠ 0) {rh rg : ℂ → ℂ}
    (hrh : AnalyticAt ℂ rh 0) (hrg : AnalyticAt ℂ rg 0)
    (hheightEnd : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → p z 2 = A/z^2+rh z)
    (hgaussEnd : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv (fun w => nullGauss (p w)) z/nullGauss (p z) = κ/z^2+rg z) :
    ∃ (a c : ℝ) (q : ℂ → Fin 3 → ℂ) (m : ℤ),
      a ∈ Ioo (0 : ℝ) 1 ∧ c ≠ 0 ∧ t < ellipticVerticalUpper ∧ a = verticalA t ∧
      (q = p ∨ q = fun z => flipNullY (p z)) ∧
      (∀ z ∉ (rhombicPeriodPair t ht).lattice,
        q z 2 = I*c*((rhombicPeriodPair t ht).weierstrassP z-
          (rhombicPeriodPair t ht).weierstrassP a)) ∧
      ((∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss (q z) = thetaGauss t a m z) ∨
       (∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss (q z) = -thetaGauss t a m z)) := by
  obtain ⟨a,c,ha,hc,htop,haBranch,hheight,_⟩ := symmetric_null_height_data_reduction ht hp hF hFP
    (fun z hz => (hanalytic z hz 2).differentiableAt) hA hrh hheightEnd
  obtain ⟨q,m,hq,_,hg⟩ := null_gauss_integer_reduction ht ha hp hanalytic
    (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)) hheight hrg hgaussEnd
  refine ⟨a,c,q,m,ha,hc,htop,haBranch,hq,?_,hg⟩
  intro z hz
  rcases hq with rfl | rfl
  · exact hheight z hz
  · exact hheight z hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.regular_symmetric_null_data_integer_reduction
