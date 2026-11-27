import TwoAxisHelicoid.HelicoidUntwistExterior

namespace TwoAxisHelicoid
open Real Set
open scoped ContDiff
set_option maxHeartbeats 1000000

/-- Prepare the actual helicoidal end for the explicit cap. The ambient
coordinate change and its inverse are smooth; its exterior is exactly
the entire plane, and every prescribed compact parameter core lies in
the retained ball. -/
theorem HasHelicoidC1End.exists_cap_normalization
    {M : Type*} [TopologicalSpace M] [T2Space M] {X : M → HelicoidTubeCoordinates}
    (hEnd : HasHelicoidC1End X) (hX : IsProperMap X) {C : Set M} (hC : IsCompact C) :
    ∃ (D : HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates) (R : ℝ), 0 < R ∧
      ContDiff ℝ (∞ : WithTop ℕ∞) D ∧ ContDiff ℝ (∞ : WithTop ℕ∞) D.symm ∧
      (∀ y, R^2 < ambientRadiusSq y → (y ∈ range (D.symm ∘ X) ↔ y.1.2 = 0)) ∧
      ∀ q ∈ C, ambientRadiusSq (D.symm (X q)) ≤ R^2 := by
  obtain ⟨Ψ,hΨ,_hfixed,hExact⟩ := hEnd.exists_smooth_ambient_straightening hX (hC.image hX.continuous)
  let ψ := Ψ ⟨1,by norm_num⟩
  let Y := ψ.symm ∘ X
  have hY : Continuous Y := ψ.symm.continuous.comp hX.continuous
  obtain ⟨R₀,hR₀,hplane⟩ := hExact.untwisted_plane_exterior hY
  let D := helicoidTubeRotation.trans ψ
  let U := D.symm ∘ X
  have hU : Continuous U := D.symm.continuous.comp hX.continuous
  obtain ⟨L,hL⟩ := (hC.image (ambientRadiusSq_continuous.comp hU)).isBounded.exists_norm_le
  let R := R₀+|L|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hR₀R : R₀ ≤ R := by dsimp [R]; linarith [abs_nonneg L]
  have hLsq : L < R^2 := by
    dsimp [R]
    nlinarith [le_abs_self L,abs_nonneg L,sq_nonneg (R₀+|L|)]
  refine ⟨D,R,hR,?_,?_,hplane R hR₀R,?_⟩
  · exact (hΨ.smooth ⟨1,by norm_num⟩).1.comp helicoidTubeRotation_contDiff
  · exact helicoidTubeRotation_symm_contDiff.comp (hΨ.smooth ⟨1,by norm_num⟩).2
  · intro q hq
    have hb := hL (ambientRadiusSq (U q)) ⟨q,hq,rfl⟩
    have hl := le_abs_self (ambientRadiusSq (U q))
    rw [Real.norm_eq_abs] at hb
    exact (hl.trans hb).trans hLsq.le

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HasHelicoidC1End.exists_cap_normalization
