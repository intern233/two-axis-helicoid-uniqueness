import TwoAxisHelicoid.CapOrthonormalSpin

namespace TwoAxisHelicoid
open Complex Set Matrix Filter
open scoped Matrix

theorem spatial_dot_self_pos {A : Fin 3 → ℝ} (hA : A ≠ 0) : 0 < A ⬝ᵥ A := by
  apply lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => mul_self_nonneg (A i)))
  exact Ne.symm (mt dotProduct_self_eq_zero.mp hA)

theorem spatialUnitVector_unit {A : Fin 3 → ℝ} (hA : A ≠ 0) :
    spatialUnitVector A ⬝ᵥ spatialUnitVector A = 1 := by
  have ha := spatial_dot_self_pos hA
  have hs := Real.sq_sqrt ha.le
  rw [spatialUnitVector,smul_dotProduct,dotProduct_smul,smul_eq_mul,smul_eq_mul]
  rw [← mul_assoc,← pow_two,inv_pow,hs]
  exact inv_mul_cancel₀ ha.ne'

theorem spatialUnitVector_neg (A : Fin 3 → ℝ) : spatialUnitVector (-A) = -spatialUnitVector A := by
  simp [spatialUnitVector]

theorem spatialGramFrame_neg (A B : Fin 3 → ℝ) :
    spatialGramFrame (-A) (-B) = (-(spatialGramFrame A B).1,-(spatialGramFrame A B).2) := by
  simp only [spatialGramFrame,neg_dotProduct,dotProduct_neg,neg_neg,spatialUnitVector_neg,smul_neg]
  rw [show -B - -(((A ⬝ᵥ B)/(A ⬝ᵥ A)) • A) = -(B-((A ⬝ᵥ B)/(A ⬝ᵥ A)) • A) by abel,spatialUnitVector_neg]

theorem gramResidual_ne_zero {D : ℂ →L[ℝ] (Fin 3 → ℝ)} (hD : Function.Injective D)
    {v : ℂ} (hv : v ≠ 0) (k : ℝ) : D (I*v)-k • D v ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  rw [← map_smul] at he
  have e := hD he
  rw [Complex.real_smul] at e
  have hi := congrArg Complex.im (mul_right_cancel₀ hv e)
  simp at hi

theorem spatialGramFrame_regular {D : ℂ →L[ℝ] (Fin 3 → ℝ)} (hD : Function.Injective D)
    {v : ℂ} (hv : v ≠ 0) : let p := spatialGramFrame (D v) (D (I*v))
      p.1 ⬝ᵥ p.1 = 1 ∧ p.2 ⬝ᵥ p.2 = 1 ∧ p.1 ⬝ᵥ p.2 = 0 := by
  have hA : D v ≠ 0 := fun he => hv (hD (he.trans D.map_zero.symm))
  let A := D v
  let B := D (I*v)
  refine ⟨spatialUnitVector_unit hA,spatialUnitVector_unit (gramResidual_ne_zero hD hv _),?_⟩
  have hAA : A ⬝ᵥ A ≠ 0 := (spatial_dot_self_pos hA).ne'
  have h0 : A ⬝ᵥ (B-((A ⬝ᵥ B)/(A ⬝ᵥ A)) • A) = 0 := by
    rw [dotProduct_sub,dotProduct_smul,smul_eq_mul,div_mul_cancel₀ _ hAA,sub_self]
  change spatialUnitVector A ⬝ᵥ spatialUnitVector (B-((A ⬝ᵥ B)/(A ⬝ᵥ A)) • A) = 0
  rw [spatialUnitVector,spatialUnitVector,smul_dotProduct,dotProduct_smul,h0,smul_zero,smul_zero]

theorem spatialUnitVector_continuous {S : Type*} [TopologicalSpace S] {A : S → Fin 3 → ℝ}
    (hA : Continuous A) (hn : ∀ s, A s ≠ 0) : Continuous (fun s => spatialUnitVector (A s)) := by
  exact (((hA.dotProduct hA).sqrt).inv₀ (fun s => (Real.sqrt_pos.mpr (spatial_dot_self_pos (hn s))).ne')).smul hA

/-- The actual Euclidean tangent frame depends continuously on a regular
family of differentials and nonvanishing directions. -/
noncomputable def spatialDifferentialFrame {D : ℂ →L[ℝ] (Fin 3 → ℝ)} (hD : Function.Injective D)
    {v : ℂ} (hv : v ≠ 0) : OrthonormalTangentPair :=
  ⟨spatialGramFrame (D v) (D (I*v)),spatialGramFrame_regular hD hv⟩

theorem spatialDifferentialFrame_continuous {S : Type*} [TopologicalSpace S]
    {D : S → ℂ →L[ℝ] (Fin 3 → ℝ)} {v : S → ℂ} (hD : Continuous D) (hv : Continuous v)
    (hi : ∀ s, Function.Injective (D s)) (hn : ∀ s, v s ≠ 0) :
    Continuous (fun s => spatialDifferentialFrame (hi s) (hn s)) := by
  let A := fun s => D s (v s)
  let B := fun s => D s (I*v s)
  have ha : Continuous A := hD.clm_apply hv
  have hb : Continuous B := hD.clm_apply (continuous_const.mul hv)
  have hAn (s) : A s ≠ 0 := fun he => hn s (hi s (he.trans (D s).map_zero.symm))
  have hk := (ha.dotProduct hb).div (ha.dotProduct ha) (fun s => (spatial_dot_self_pos (hAn s)).ne')
  exact ((spatialUnitVector_continuous ha hAn).prodMk
    (spatialUnitVector_continuous (hb.sub (hk.smul ha)) (fun s => gramResidual_ne_zero (hi s) (hn s) _))).subtype_mk _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.spatialDifferentialFrame_continuous
