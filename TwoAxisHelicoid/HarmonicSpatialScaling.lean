import TwoAxisHelicoid.HarmonicTorusC1Normalization

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- A nonzero real spatial homothety preserves the two actual symmetry
actions, harmonicity, conformality and immersion of the lifted map. -/
theorem TwoAxisHarmonicConformalImmersion.spatial_smul {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) {k : ℝ} (hk : k ≠ 0) :
    TwoAxisHarmonicConformalImmersion L (fun z => k • X z) := by
  refine ⟨fun z hz => (hX.differentiable z hz).const_smul k,?_,?_,?_,?_,?_,?_⟩
  · intro z hz j
    exact (hX.harmonic z hz j).comp_CLM (k • ContinuousLinearMap.id ℝ ℝ)
  · intro z hz
    have hd (j : Fin 3) : fderiv ℝ (fun w => (k • X w) j) z = k • fderiv ℝ (fun w => X w j) z := by
      have hj : DifferentiableAt ℝ (fun w => X w j) z := differentiableAt_pi.mp (hX.differentiable z hz) j
      exact (hj.hasFDerivAt.const_smul k).fderiv
    obtain ⟨h₁,h₂⟩ := hX.conformal z hz
    unfold ConformalCoordinateDerivatives
    simp only [hd,smul_apply,smul_eq_mul]
    constructor
    · simpa only [mul_pow,← Finset.mul_sum] using congrArg (k^2*·) h₁
    · calc
        _ = k^2 * ∑ j : Fin 3, fderiv ℝ (fun w => X w j) z 1 * fderiv ℝ (fun w => X w j) z I := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [h₂,mul_zero]
  · intro z hz u v h
    have hd : fderiv ℝ (fun w => k • X w) z = k • fderiv ℝ X z := ((hX.differentiable z hz).hasFDerivAt.const_smul k).fderiv
    rw [hd] at h
    exact hX.immersion z hz ((smul_right_injective _ hk) h)
  · intro z hz ω hω
    rw [hX.periodic z hz ω hω]
  · intro z hz
    rw [hX.neg z hz]
    ext j
    fin_cases j <;> simp
  · intro z hz
    rw [hX.conjugation z hz]
    ext j
    fin_cases j <;> simp

theorem harmonic_quotient_injective_of_smul {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) (hi : Function.Injective (harmonicTorusImmersion hX))
    {k : ℝ} (hk : k ≠ 0) : Function.Injective (harmonicTorusImmersion (hX.spatial_smul hk)) := by
  have he := harmonicTorusImmersion_space_map hX (Homeomorph.smulOfNeZero k hk) (hX.spatial_smul hk)
  intro a b hab
  apply hi
  apply (Homeomorph.smulOfNeZero k hk).injective
  exact (congrFun he a).symm.trans (hab.trans (congrFun he b))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.TwoAxisHarmonicConformalImmersion.spatial_smul
