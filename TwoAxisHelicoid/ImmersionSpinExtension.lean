import TwoAxisHelicoid.MultiplierSpinRestriction

namespace TwoAxisHelicoid
open Complex Set
set_option maxHeartbeats 1000000

noncomputable def restrictedCompactSpinPhase (L : PeriodPair) (χ : L.lattice →+ ZMod 2)
    (u : Circle) (x : RestrictedCompactMultiplierSpin L χ) : RestrictedCompactMultiplierSpin L χ :=
  ⟨associatedSpinPhase _ (latticeSignCoverDeck_involutive L χ) u x.1,by
    change (associatedSpinProjection _ _ _ _ (associatedSpinPhase _ _ _ _)).1 ≠ 0
    rw [associatedSpinProjection_phase]
    exact x.2⟩

variable {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)

/-- A compact extension of the ambient spin structure of the actual
immersed punctured torus. All spin frames and the square map are kept. -/
noncomputable def harmonic_integer_compact_spin_restriction :
    RestrictedCompactMultiplierSpin (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m) ≃ₜ
      ImmersionSpatialSpin (rhombicPeriodPair t ht) X :=
  (multiplierSpinRestrictionHomeomorph _ _).symm.trans
    (harmonic_integer_induced_spin_homeomorph ht ha hc m hC0 hC hX hh hg)

theorem harmonic_integer_compact_spin_square
    (s : RestrictedCompactMultiplierSpin (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) :
    let e := harmonic_integer_compact_spin_restriction ht ha hc m hC0 hC hX hh hg s
    let y := compactMultiplierSpinProjection _ _ s.1
    e.1.1.1 = y.1 ∧ unitQuaternionFrame e.1.2 =
      rotateTangentPair y.2 (weierstrassTorusFrame ht ha m hC0 e.1.1) := by
  let L := rhombicPeriodPair t ht
  let χ := latticeSpinParity L m
  obtain ⟨w,rfl⟩ := (multiplierSpinRestrictionHomeomorph L χ).surjective s
  obtain ⟨⟨q,u⟩,rfl⟩ := Quotient.exists_rep w
  simp only [χ,L,harmonic_integer_compact_spin_restriction,Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  rw [multiplierSpinRestrictionHomeomorph_mk]
  have he := weierstrassSpatialSpinHomeomorph_proj ht ha m hC0 q u
  have hb := congrArg Prod.fst he
  have hf := congrArg Prod.snd he
  constructor
  · exact congrArg Subtype.val hb
  · change unitQuaternionFrame (weierstrassSpatialSpinHomeomorph ht ha m hC0 (Quotient.mk _ (q,u))).1.2 = rotateTangentPair (u^2)
      (weierstrassTorusFrame ht ha m hC0 (weierstrassSpatialSpinHomeomorph ht ha m hC0
        (Quotient.mk _ (q,u))).1.1)
    change (weierstrassSpatialSpinHomeomorph ht ha m hC0 (Quotient.mk _ (q,u))).1.1 =
      puncturedSignCoverProjection _ _ q at hb
    rw [hb]
    exact hf

theorem harmonic_integer_compact_spin_phase (u : Circle)
    (s : RestrictedCompactMultiplierSpin (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) :
    (harmonic_integer_compact_spin_restriction ht ha hc m hC0 hC hX hh hg
      (restrictedCompactSpinPhase _ _ u s)).1.2 =
    spinCircleAction u (harmonic_integer_compact_spin_restriction ht ha hc m hC0 hC hX hh hg s).1.2 := by
  let L := rhombicPeriodPair t ht
  let χ := latticeSpinParity L m
  obtain ⟨w,rfl⟩ := (multiplierSpinRestrictionHomeomorph L χ).surjective s
  have he : restrictedCompactSpinPhase L χ u (multiplierSpinRestrictionHomeomorph L χ w) =
      multiplierSpinRestrictionHomeomorph L χ (associatedSpinPhase _ (puncturedSignCoverDeck_involutive L χ) u w) :=
    Subtype.ext (multiplierSpinRestrictionHomeomorph_phase L χ u w).symm
  rw [he]
  simp only [χ,L,harmonic_integer_compact_spin_restriction,Homeomorph.trans_apply,Homeomorph.symm_apply_apply]
  exact harmonic_integer_induced_spin_phase ht ha hc m hC0 hC hX hh hg u w

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_compact_spin_square
#print axioms TwoAxisHelicoid.harmonic_integer_compact_spin_phase
