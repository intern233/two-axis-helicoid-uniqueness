import TwoAxisHelicoid.UnitSpinorFrameCover

namespace TwoAxisHelicoid
open Set Topology

@[instance_reducible] noncomputable def involutionSignAction {E : Type*} [TopologicalSpace E]
    (τ : E ≃ₜ E) (hτ : Function.Involutive τ) : AddAction (ZMod 2) E where
  vadd g x := if g = 0 then x else τ x
  zero_vadd x := by
    change (if (0 : ZMod 2) = 0 then x else τ x) = x
    simp
  add_vadd g h x := by
    change (if g+h = 0 then x else τ x) =
      (if g = 0 then (if h = 0 then x else τ x) else τ (if h = 0 then x else τ x))
    rcases zmod_two_cases g with rfl | rfl <;> rcases zmod_two_cases h with rfl | rfl <;>
      simp [show (1 : ZMod 2)+1 = 0 from by decide]
    exact (hτ x).symm

/-- A free involution with quotient topology gives a genuine twofold
covering. The proof uses separated neighborhoods, with no compactness
or metrizability assumption on the total space. -/
theorem free_involution_quotient_isCoveringMap
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] [T2Space E]
    (τ : E ≃ₜ E) (hτ : Function.Involutive τ) (hne : ∀ x, τ x ≠ x)
    {p : E → B} (hp : IsQuotientMap p)
    (hf : ∀ x y, p x = p y ↔ x = y ∨ x = τ y) : IsCoveringMap p := by
  let := involutionSignAction τ hτ
  have hzero (x : E) : (0 : ZMod 2) +ᵥ x = x := zero_vadd _ _
  have hone (x : E) : (1 : ZMod 2) +ᵥ x = τ x := by
    change (if (1 : ZMod 2) = 0 then x else τ x) = τ x
    norm_num
  let : ContinuousConstVAdd (ZMod 2) E := ⟨fun g => by
    rcases zmod_two_cases g with rfl | rfl
    · simpa only [hzero] using! (continuous_id : Continuous (id : E → E))
    · simpa only [hone] using! τ.continuous⟩
  have hc : IsAddQuotientCoveringMap p (ZMod 2) := {
    toIsQuotientMap := hp
    continuous_const_vadd := continuous_const_vadd
    apply_eq_iff_mem_orbit := by
      intro x y
      rw [hf]
      constructor
      · rintro (he | he)
        · exact ⟨0,by simpa only [hzero] using he.symm⟩
        · exact ⟨1,by simpa only [hone] using he.symm⟩
      · rintro ⟨g,hg⟩
        rcases zmod_two_cases g with rfl | rfl
        · exact Or.inl (by simpa only [hzero] using hg.symm)
        · exact Or.inr (by simpa only [hone] using hg.symm)
    disjoint := fun x => by
      obtain ⟨U,V,hU,hV,hx,hτx,hUV⟩ := t2_separation (Ne.symm (hne x))
      refine ⟨U ∩ τ ⁻¹' V,(hU.inter (hV.preimage τ.continuous)).mem_nhds ⟨hx,hτx⟩,?_⟩
      intro g hg
      rcases zmod_two_cases g with rfl | rfl
      · rfl
      · exfalso
        obtain ⟨w,⟨z,hz,hzw⟩,hw⟩ := hg
        change (1 : ZMod 2) +ᵥ z = w at hzw
        rw [hone] at hzw
        have hwV : w ∈ V := hzw ▸ hz.2
        exact Set.disjoint_left.mp hUV hw.1 hwV }
  exact hc.isCoveringMap

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.free_involution_quotient_isCoveringMap
