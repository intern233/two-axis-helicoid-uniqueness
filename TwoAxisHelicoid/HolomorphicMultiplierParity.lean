import TwoAxisHelicoid.MultiplierLineSections
import TwoAxisHelicoid.GenusOneSpinQuadratic

namespace TwoAxisHelicoid
open Complex

theorem flat_section_lattice_character {t : ℝ} (ht : 0 < t) (m : ℤ)
    (f : flatHolomorphicSections t 1 ((-1 : ℂ)^m)) (z : ℂ) (ω : (rhombicPeriodPair t ht).lattice) :
    f.1 (z+ω.1) = paritySign (latticeSpinParity (rhombicPeriodPair t ht) m ω)*f.1 z := by
  let L := rhombicPeriodPair t ht
  let p := L.latticeEquivProd ω
  have hω : ω.1 = (p.1 : ℂ)*2+(p.2 : ℂ)*(1+I*t) := by
    have h := L.latticeEquiv_symm_apply p
    rw [L.latticeEquivProd.symm_apply_apply] at h
    exact h
  have h₁ : Function.Periodic f.1 2 := fun w => by simpa using f.2.2.1 w
  have h₂ := multiplicative_quasiperiod_int (zpow_ne_zero m (by norm_num : (-1 : ℂ) ≠ 0))
    f.2.2.2 p.2 (z+(p.1 : ℂ)*2)
  have he := h₁.zsmul p.1 z
  simp only [zsmul_eq_mul] at he
  rw [← zpow_mul,he] at h₂
  rw [hω,latticeSpinParity_sign]
  simpa only [integerSpinCharacter,add_assoc] using h₂

noncomputable def holomorphicMultiplierSectionEquiv {t : ℝ} (ht : 0 < t) (m : ℤ) :
    holomorphicMultiplierSections (rhombicPeriodPair t ht) (latticeSpinParity (rhombicPeriodPair t ht) m)
      ≃ₗ[ℂ] flatHolomorphicSections t 1 ((-1 : ℂ)^m) := by
  let L := rhombicPeriodPair t ht
  let χ := latticeSpinParity L m
  refine {
    toFun := fun S => ⟨multiplierSectionPlane L χ S.1,S.2,?_,?_⟩
    invFun := fun f => ⟨multiplierSectionFromScalar L χ f.1 (flat_section_lattice_character ht m f),?_⟩
    left_inv := ?_
    right_inv := ?_
    map_add' := fun _ _ => Subtype.ext rfl
    map_smul' := fun _ _ => Subtype.ext rfl }
  · intro z
    have h := multiplierSectionPlane_translate L χ S.1 z (periodGeneratorPeriod L 0)
    rw [periodGeneratorPeriod_val,latticeSpinParity_generator] at h
    simpa [L,rhombicPeriodPair,paritySign_zero] using h
  · intro z
    have h := multiplierSectionPlane_translate L χ S.1 z (periodGeneratorPeriod L 1)
    rw [periodGeneratorPeriod_val,latticeSpinParity_generator] at h
    simpa [L,rhombicPeriodPair,paritySign_intCast] using h
  · change Differentiable ℂ (multiplierSectionPlane L χ _)
    rw [multiplierSectionFromScalar_plane]
    exact f.2.1
  · intro S
    apply Subtype.ext
    apply multiplierSectionPlane_injective
    exact multiplierSectionFromScalar_plane _ _ _ _
  · intro f
    apply Subtype.ext
    exact multiplierSectionFromScalar_plane L χ f.1 (flat_section_lattice_character ht m f)

/-- The analytic parity belongs to actual holomorphic sections of the
associated complex lines over the compact torus. -/
theorem holomorphicMultiplierSection_finrank {t : ℝ} (ht : 0 < t) (m : ℤ) :
    Module.finrank ℂ (holomorphicMultiplierSections (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) = if Even m then 1 else 0 := by
  rw [(holomorphicMultiplierSectionEquiv ht m).finrank_eq,integerSpinorSections_finrank ht m]

theorem integerGeneratorQuadratic_arf_eq_line_sections {t : ℝ} (ht : 0 < t) (m : ℤ)
    {v w : ZMod 2 × ZMod 2} (h : torusIntersectionModTwo v w = 1) :
    integerGeneratorQuadratic m v*integerGeneratorQuadratic m w =
      (Module.finrank ℂ (holomorphicMultiplierSections (rhombicPeriodPair t ht)
        (latticeSpinParity (rhombicPeriodPair t ht) m)) : ZMod 2) := by
  rw [(holomorphicMultiplierSectionEquiv ht m).finrank_eq]
  exact integerGeneratorQuadratic_arf_eq_section_parity ht m h

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.holomorphicMultiplierSection_finrank
#print axioms TwoAxisHelicoid.integerGeneratorQuadratic_arf_eq_line_sections
