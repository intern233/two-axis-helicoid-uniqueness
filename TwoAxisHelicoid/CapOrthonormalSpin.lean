import TwoAxisHelicoid.CapGeneratorQuadratic

namespace TwoAxisHelicoid
open Complex Set Matrix
open scoped Matrix

/-- Unit normalization for the Euclidean spatial scalar product. -/
noncomputable def spatialUnitVector (A : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (Real.sqrt (A ⬝ᵥ A))⁻¹ • A

/-- The oriented Gram--Schmidt frame. The first argument is the tangent
to a marked curve and the second is its positively transverse tangent. -/
noncomputable def spatialGramFrame (A B : Fin 3 → ℝ) :
    (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  (spatialUnitVector A, spatialUnitVector (B - ((A ⬝ᵥ B)/(A ⬝ᵥ A)) • A))

theorem spatialUnitVector_eq_of_normalized {A : Fin 3 → ℝ} {k : ℝ} (hk : 0 < k)
    (h : (k • A) ⬝ᵥ (k • A) = 1) : spatialUnitVector A = k • A := by
  have h1 : k*(k*(A ⬝ᵥ A)) = 1 := by
    simpa only [smul_dotProduct,dotProduct_smul,smul_eq_mul] using h
  have hpos : 0 < A ⬝ᵥ A := by
    by_contra! hh
    linarith [mul_nonpos_of_nonneg_of_nonpos hk.le (mul_nonpos_of_nonneg_of_nonpos hk.le hh)]
  have hsq := Real.sq_sqrt hpos.le
  have hkn : 0 ≤ k * Real.sqrt (A ⬝ᵥ A) := mul_nonneg hk.le (Real.sqrt_nonneg _)
  have he : (k * Real.sqrt (A ⬝ᵥ A))^2 = 1 := by
    rw [mul_pow,hsq,pow_two,mul_assoc,h1]
  have hunit : k * Real.sqrt (A ⬝ᵥ A) = 1 := by nlinarith
  unfold spatialUnitVector
  rw [← eq_inv_of_mul_eq_one_left hunit]

theorem spatialGramFrame_eq_of_conformal (p : OrthonormalTangentPair)
    {A B : Fin 3 → ℝ} {k : ℝ} (hk : 0 < k) (h : p.1 = (k • A,k • B)) :
    spatialGramFrame A B = p.1 := by
  obtain ⟨hA,hB,hAB⟩ := p.2
  rw [h] at hA hB hAB ⊢
  have hdot : A ⬝ᵥ B = 0 := by
    have he : k*(k*(A ⬝ᵥ B)) = 0 := by simpa only [smul_dotProduct,dotProduct_smul,smul_eq_mul] using hAB
    exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hk.ne')).resolve_left hk.ne'
  simp only [spatialGramFrame,hdot,zero_div,zero_smul,sub_zero,
    spatialUnitVector_eq_of_normalized hk hA,spatialUnitVector_eq_of_normalized hk hB]

/-- The ambient spin structure evaluates on a marked simple closed
curve by lifting its orthonormal, oriented, tangent-adapted Euclidean frame. -/
def CapGeneratorAmbientSpinCloses (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ) (i : Fin 2) : Prop :=
  ∃ q : C(unitInterval,UnitQuaternion), q 1 = q 0 ∧ ∀ r : unitInterval,
    let D := fderiv ℝ (F ∘ periodTorusProjection L) (periodBasisLine L i r)
    (unitQuaternionFrame (q r)).1 = spatialGramFrame (D (L.basis i)) (D (I*L.basis i))

/-- If the pulled-back actual metric is conformal on the generator,
the ambient Euclidean Gram--Schmidt test agrees with the normalized
derivative test. Nothing is required of the surface elsewhere. -/
theorem ambient_generator_spin_closes_iff {L : PeriodPair} {F : PeriodTorus L → Fin 3 → ℝ} {i : Fin 2}
    (h : ∀ r : unitInterval, ∃ (p : OrthonormalTangentPair) (k : ℝ), 0 < k ∧
      p.1 = (k • fderiv ℝ (F ∘ periodTorusProjection L) (periodBasisLine L i r) (L.basis i),
        k • fderiv ℝ (F ∘ periodTorusProjection L) (periodBasisLine L i r) (I*L.basis i))) :
    CapGeneratorAmbientSpinCloses L F i ↔ CapGeneratorHasClosedSpinLift L F i := by
  constructor
  · rintro ⟨q,he,hq⟩
    refine ⟨q,he,fun r => ?_⟩
    obtain ⟨p,k,hk,hp⟩ := h r
    exact ⟨k,hk,(hq r).trans ((spatialGramFrame_eq_of_conformal p hk hp).trans hp)⟩
  · rintro ⟨q,he,hq⟩
    refine ⟨q,he,fun r => ?_⟩
    obtain ⟨k,hk,hp⟩ := hq r
    exact (spatialGramFrame_eq_of_conformal _ hk hp).symm

noncomputable def capAmbientSpinQuadratic (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ) :
    ZMod 2 × ZMod 2 → ZMod 2 := by
  classical
  exact torusQuadratic (if CapGeneratorAmbientSpinCloses L F 0 then 1 else 0)
    (if CapGeneratorAmbientSpinCloses L F 1 then 1 else 0)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ambient_generator_spin_closes_iff
