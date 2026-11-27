import TwoAxisHelicoid.CoordinateSignMaps

namespace TwoAxisHelicoid
open Complex Set InnerProductSpace

/-- Ambient coordinate reflections preserve the actual harmonic,
conformal, immersed and two-axis symmetric map. -/
theorem TwoAxisHarmonicConformalImmersion.coordinateSigns
    {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X)
    {s : Fin 3 → ℝ} (hs : ∀ j, (s j)^2 = 1) :
    TwoAxisHarmonicConformalImmersion L (fun z => coordinateSignMap s (X z)) where
  differentiable z hz := (coordinateSignMap s).differentiableAt.comp z (hX.differentiable z hz)
  harmonic z hz j := by
    change HarmonicAt (s j • fun w => X w j) z
    exact (hX.harmonic z hz j).const_smul
  conformal z hz := by
    have he j : fderiv ℝ (fun w => coordinateSignMap s (X w) j) z =
        s j • fderiv ℝ (fun w => X w j) z :=
      ((((hX.harmonic z hz j).1.differentiableAt two_ne_zero).hasFDerivAt).const_mul (s j)).fderiv
    have hsq (v : ℂ) : (∑ j : Fin 3, (s j*fderiv ℝ (fun w => X w j) z v)^2) =
        ∑ j : Fin 3, (fderiv ℝ (fun w => X w j) z v)^2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [mul_pow,hs j,one_mul]
    have hcross : (∑ j : Fin 3, (s j*fderiv ℝ (fun w => X w j) z 1)*
        (s j*fderiv ℝ (fun w => X w j) z I)) =
        ∑ j : Fin 3, fderiv ℝ (fun w => X w j) z 1*fderiv ℝ (fun w => X w j) z I := by
      apply Finset.sum_congr rfl
      intro j _hj
      calc
        _ = (s j)^2*(fderiv ℝ (fun w => X w j) z 1*fderiv ℝ (fun w => X w j) z I) := by ring
        _ = _ := by rw [hs j,one_mul]
    simpa only [ConformalCoordinateDerivatives,he,smul_apply,smul_eq_mul,hsq,hcross] using hX.conformal z hz
  immersion z hz := by
    change Function.Injective (fderiv ℝ (coordinateSignMap s ∘ X) z)
    rw [((coordinateSignMap s).hasFDerivAt.comp z (hX.differentiable z hz).hasFDerivAt).fderiv]
    exact (coordinateSignMap_involutive hs).injective.comp (hX.immersion z hz)
  periodic z hz ω hω := by rw [hX.periodic z hz ω hω]
  neg z hz := by
    rw [hX.neg z hz]
    ext j
    fin_cases j <;> simp [coordinateSignMap_apply]
  conjugation z hz := by
    rw [hX.conjugation z hz]
    ext j
    fin_cases j <;> simp [coordinateSignMap_apply]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.TwoAxisHarmonicConformalImmersion.coordinateSigns
