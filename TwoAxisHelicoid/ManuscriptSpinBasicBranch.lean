import TwoAxisHelicoid.PinkallHelicoidSpinParity
import TwoAxisHelicoid.HoffmanWhiteWindingReduction

namespace TwoAxisHelicoid
open Complex Set

/-- The last step of §4.5 in the manuscript. The intersection argument
restricts the index to zero or one. The ambient and holomorphic spin
structures on the very same embedded cap make that index odd. -/
theorem manuscript_integer_one_via_even_spin (hPinkall : PinkallEmbeddedTorusRegularHomotopy) (hHW : RhombicHelicoidIntersectionPrinciple)
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    m = 1 := by
  have hodd := actual_embedded_integer_branch_odd_of_pinkall hPinkall ht ha hc m hX hXi hh hg
  rcases integer_branch_zero_or_one_of_intersection_principle hHW ht ha hc m hX hXi hh hg with h | h
  · subst m
    simp at hodd
  · exact h

/-- Necessary basic data for any injective two-axis harmonic conformal
torus with the two meromorphic double poles. The derivation uses the
ambient spin exclusion in §4.5 and the geometric intersection in §4.2. -/
theorem manuscript_corollary_4_5_via_even_spin (hPinkall : PinkallEmbeddedTorusRegularHomotopy)
    (hHW : RhombicHelicoidIntersectionPrinciple)
    {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    ∃ (a c : ℝ) (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)),
      a ∈ Ioo (0 : ℝ) 1 ∧ c ≠ 0 ∧ t < ellipticVerticalUpper ∧ a = verticalA t ∧
      (∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) ∧
      TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) (fun z => R (X z)) ∧
      (∀ z ∉ (rhombicPeriodPair t ht).lattice,
        puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun z => R (X z)) z 2 =
          coordinateData t a c ht z 2) ∧
      ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun z => R (X z)) z) =
          thetaGauss t a 1 z := by
  obtain ⟨a,c,m,R,ha,hc,hT,ha',hR,hY,hh,hg⟩ :=
    harmonic_meromorphic_oriented_integer_data ht hX hhOrder hgOrder
  have hYi : Function.Injective (harmonicTorusImmersion hY) := by
    rw [harmonicTorusImmersion_space_map hX R hY]
    exact R.injective.comp hXi
  have hm := manuscript_integer_one_via_even_spin hPinkall hHW ht ha hc m hY hYi hh hg
  subst m
  exact ⟨a,c,R,ha,hc,hT,ha',hR,hY,hh,hg⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.manuscript_integer_one_via_even_spin
#print axioms TwoAxisHelicoid.manuscript_corollary_4_5_via_even_spin
