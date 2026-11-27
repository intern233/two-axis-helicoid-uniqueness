import TwoAxisHelicoid.HarmonicGaussOrientation
import TwoAxisHelicoid.MeromorphicNullEndReduction

namespace TwoAxisHelicoid
open Complex Set

/-- The coefficient and Gauss-sign alternatives in the meromorphic
classification are realized by actual fixed Euclidean isometries of the
harmonic map. The integer branch remains unrestricted. -/
theorem harmonic_meromorphic_oriented_integer_data {t : ℝ} (ht : 0 < t)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    ∃ (a c : ℝ) (m : ℤ) (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)),
      a ∈ Ioo (0 : ℝ) 1 ∧ c ≠ 0 ∧ t < ellipticVerticalUpper ∧ a = verticalA t ∧
      (∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) ∧
      TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) (fun z => R (X z)) ∧
      (∀ z ∉ (rhombicPeriodPair t ht).lattice,
        puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun z => R (X z)) z 2 =
          I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a)) ∧
      ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun z => R (X z)) z) =
          thetaGauss t a m z := by
  obtain ⟨a,c,q,m,ha,hc,htu,haB,hq,hheight,hgauss⟩ :=
    harmonic_meromorphic_integer_data_reduction ht hX hhOrder hgOrder
  obtain ⟨R,hR,hY,hcoeff⟩ := harmonic_coefficient_orientation_isometry hX hq
  have hhY z (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun z => R (X z)) z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a) := by
    rw [hcoeff z hz]
    exact hheight z hz
  rcases hgauss with hpos | hneg
  · refine ⟨a,c,m,R,ha,hc,htu,haB,hR,hY,hhY,?_⟩
    intro z hz
    rw [hcoeff z ((not_mem_gaussLogPoleSet _ _ _).mp hz).1]
    exact hpos z hz
  · let R' := R.trans (coordinateSignHomeomorph verticalHalfTurnSigns_sq)
    refine ⟨a,c,m,R',ha,hc,htu,haB,?_,hY.coordinateSigns verticalHalfTurnSigns_sq,?_,?_⟩
    · intro v w
      change (∑ j, (coordinateSignMap verticalHalfTurnSigns (R v) j-
        coordinateSignMap verticalHalfTurnSigns (R w) j)^2) = _
      rw [coordinateSignMap_squared_displacement verticalHalfTurnSigns_sq,hR]
    · intro z hz
      change puncturedImmersionCoefficient (rhombicPeriodPair t ht)
        (fun z => coordinateSignMap verticalHalfTurnSigns (R (X z))) z 2 = _
      rw [punctured_coefficient_vertical_half_turn hY hz]
      exact hhY z hz
    · intro z hz
      have hzn := ((not_mem_gaussLogPoleSet _ _ _).mp hz).1
      change nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht)
        (fun z => coordinateSignMap verticalHalfTurnSigns (R (X z))) z) = _
      rw [punctured_coefficient_vertical_half_turn hY hzn,nullGauss_vertical_half_turn,
        hcoeff z hzn,hneg z hz,neg_neg]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_meromorphic_oriented_integer_data
