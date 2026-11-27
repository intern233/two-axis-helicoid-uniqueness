import TwoAxisHelicoid.SpatialGramFrames

namespace TwoAxisHelicoid
open Complex Set Matrix
open scoped Matrix

theorem spatialUnitVector_mem_iff (K : Submodule ℝ (Fin 3 → ℝ)) (v : Fin 3 → ℝ) :
    spatialUnitVector v ∈ K ↔ v ∈ K := by
  by_cases hv : v = 0
  · simp [hv,spatialUnitVector]
  have hs : Real.sqrt (v ⬝ᵥ v) ≠ 0 := (Real.sqrt_pos.mpr (spatial_dot_self_pos hv)).ne'
  constructor
  · intro h
    have hh := K.smul_mem (Real.sqrt (v ⬝ᵥ v)) h
    simpa only [spatialUnitVector,smul_smul,mul_inv_cancel₀ hs,one_smul] using hh
  · exact fun h => K.smul_mem _ h

/-- The Gram frame spans the same real plane as the actual spatial
differential. The criterion also applies to degenerate vector pairs. -/
theorem spatialGramFrame_mem_iff (K : Submodule ℝ (Fin 3 → ℝ)) (A B : Fin 3 → ℝ) :
    (spatialGramFrame A B).1 ∈ K ∧ (spatialGramFrame A B).2 ∈ K ↔ A ∈ K ∧ B ∈ K := by
  simp only [spatialGramFrame,spatialUnitVector_mem_iff]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨ha,by simpa only [sub_add_cancel] using K.add_mem hb (K.smul_mem ((A ⬝ᵥ B)/(A ⬝ᵥ A)) ha)⟩
  · rintro ⟨ha,hb⟩
    exact ⟨ha,K.sub_mem hb (K.smul_mem _ ha)⟩

theorem spatialUnitVector_pos_smul {A : Fin 3 → ℝ} {r : ℝ} (hr : 0 < r) :
    spatialUnitVector (r • A) = spatialUnitVector A := by
  by_cases ha : A = 0
  · simp [ha]
  have H := spatialUnitVector_unit ha
  have hA : Real.sqrt (A ⬝ᵥ A) ≠ 0 := (Real.sqrt_pos.mpr (spatial_dot_self_pos ha)).ne'
  let k := (Real.sqrt (A ⬝ᵥ A))⁻¹ / r
  have hk : 0 < k := div_pos (inv_pos.mpr (Real.sqrt_pos.mpr (spatial_dot_self_pos ha))) hr
  have he : k • (r • A) = spatialUnitVector A := by
    rw [smul_smul]
    change (((Real.sqrt (A ⬝ᵥ A))⁻¹/r)*r) • A = _
    rw [div_mul_cancel₀ _ hr.ne']
    rfl
  exact (spatialUnitVector_eq_of_normalized hk (by rw [he]; exact H)).trans he

/-- If the first directions match, transverse tangent planes give
non-antipodal second directions along the intersection. -/
theorem transverse_differential_frames_ne_opposite
    {D E : ℂ →L[ℝ] (Fin 3 → ℝ)} {u v : ℂ} (hi : Function.Injective D) (hj : Function.Injective E)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hfirst : (spatialDifferentialFrame hi hu).1.1 = (spatialDifferentialFrame hj hv).1.1)
    (htrans : E (I*v) ∉ LinearMap.range D.toLinearMap) :
    (spatialDifferentialFrame hj hv).1.2 ≠ -(spatialDifferentialFrame hi hu).1.2 := by
  let K := LinearMap.range D.toLinearMap
  have hmem : (spatialDifferentialFrame hi hu).1.1 ∈ K ∧ (spatialDifferentialFrame hi hu).1.2 ∈ K :=
    (spatialGramFrame_mem_iff K _ _).mpr ⟨⟨u,rfl⟩,⟨I*u,rfl⟩⟩
  intro he
  apply htrans
  apply ((spatialGramFrame_mem_iff K (E v) (E (I*v))).mp ?_).2
  exact ⟨hfirst ▸ hmem.1,he.symm ▸ K.neg_mem hmem.2⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.transverse_differential_frames_ne_opposite
