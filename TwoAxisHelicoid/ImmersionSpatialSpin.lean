import TwoAxisHelicoid.SpatialTangentSpinCover

namespace TwoAxisHelicoid
open Complex Matrix Set
open scoped Matrix

theorem tangentPairNormal_dot_self (p : OrthonormalTangentPair) :
    tangentPairNormal p ⬝ᵥ tangentPairNormal p = 1 := by
  rw [tangentPairNormal,cross_dot_cross,p.2.1,p.2.2.1,p.2.2.2,one_mul,zero_mul,sub_zero]

theorem tangentPairNormal_iff_positive_scale (p q : OrthonormalTangentPair)
    (n : Fin 3 → ℝ) {k : ℝ} (hk : 0 < k) (hp : tangentPairNormal p = k • n) :
    tangentPairNormal p = tangentPairNormal q ↔ ∃ s : ℝ, 0 < s ∧ tangentPairNormal q = s • n := by
  constructor
  · intro he
    exact ⟨k,hk,he.symm.trans hp⟩
  · rintro ⟨s,hs,hq⟩
    have he : tangentPairNormal q = (s/k) • tangentPairNormal p := by
      rw [hq,hp,smul_smul,div_mul_cancel₀ _ hk.ne']
    have hd := tangentPairNormal_dot_self q
    rw [he,smul_dotProduct,dotProduct_smul,tangentPairNormal_dot_self,smul_eq_mul,smul_eq_mul,
      mul_one] at hd
    have hr : s/k = 1 := by nlinarith [div_pos hs hk]
    rw [he,hr,one_smul]

/-- The ambient quaternion spin frames selected directly by the oriented
derivative plane of an immersion on the lattice cover. -/
abbrev ImmersionSpatialSpin (L : PeriodPair) (X : ℂ → Fin 3 → ℝ) :=
  {v : PuncturedPeriodTorus L × UnitQuaternion //
    ∃ z : PuncturedLatticePlane L, puncturedPlaneProjection L z = v.1 ∧
      ∃ k : ℝ, 0 < k ∧ tangentPairNormal (unitQuaternionFrame v.2) =
        k • (fderiv ℝ X z.1 1 ⨯₃ fderiv ℝ X z.1 I)}

variable {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)

include hc hC hX hh hg in
theorem harmonic_integer_frame_normal (z : PuncturedLatticePlane (rhombicPeriodPair t ht)) :
    ∃ k : ℝ, 0 < k ∧ tangentPairNormal
      (weierstrassTorusFrame ht ha m hC0 (puncturedPlaneProjection _ z)) =
      k • (fderiv ℝ X z.1 1 ⨯₃ fderiv ℝ X z.1 I) := by
  let K := (spinorWeight (weierstrassSpinorPair t a m C z.1))⁻¹
  have hK : 0 < K := inv_pos.mpr (spinorWeight_pos (weierstrassSpinorPair_ne_zero ht ha m hC0 z.2))
  refine ⟨K*K,mul_pos hK hK,?_⟩
  rw [tangentPairNormal,harmonic_integer_torus_frame_derivative ht ha hc m hC0 hC hX hh hg]
  change (K • fderiv ℝ X z.1 1) ⨯₃ (K • fderiv ℝ X z.1 I) = _
  simp only [map_smul,LinearMap.smul_apply,smul_smul]

noncomputable def harmonic_integer_spatial_spin_equiv :
    SpatialPlaneSpin (weierstrassTorusFrame ht ha m hC0) ≃ₜ
      ImmersionSpatialSpin (rhombicPeriodPair t ht) X :=
  Homeomorph.setCongr (by
    ext v
    change tangentPairNormal (weierstrassTorusFrame ht ha m hC0 v.1) =
      tangentPairNormal (unitQuaternionFrame v.2) ↔ _
    constructor
    · intro hv
      obtain ⟨z,hz⟩ := puncturedPlaneProjection_surjective (rhombicPeriodPair t ht) v.1
      obtain ⟨k,hk,hn⟩ := harmonic_integer_frame_normal ht ha hc m hC0 hC hX hh hg z
      rw [hz] at hn
      exact ⟨z,hz,k,hk,hv.symm.trans hn⟩
    · rintro ⟨z,hz,hs⟩
      obtain ⟨k,hk,hn⟩ := harmonic_integer_frame_normal ht ha hc m hC0 hC hX hh hg z
      rw [hz] at hn
      exact (tangentPairNormal_iff_positive_scale _ _ _ hk hn).mpr hs)

noncomputable def harmonic_integer_induced_spin_homeomorph :
    PuncturedMultiplierSpinBundle (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m) ≃ₜ
      ImmersionSpatialSpin (rhombicPeriodPair t ht) X :=
  (weierstrassSpatialSpinHomeomorph ht ha m hC0).trans
    (harmonic_integer_spatial_spin_equiv ht ha hc m hC0 hC hX hh hg)

include hc hC hX hh hg in
theorem harmonic_integer_induced_spin_phase (v : Circle)
    (x : PuncturedMultiplierSpinBundle (rhombicPeriodPair t ht)
      (latticeSpinParity (rhombicPeriodPair t ht) m)) :
    (harmonic_integer_induced_spin_homeomorph ht ha hc m hC0 hC hX hh hg
      (associatedSpinPhase _ (puncturedSignCoverDeck_involutive _ _) v x)).1.2 =
      spinCircleAction v (harmonic_integer_induced_spin_homeomorph ht ha hc m hC0 hC hX hh hg x).1.2 :=
  weierstrassFrameSpinHomeomorph_equivariant ht ha m hC0 v x

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_induced_spin_homeomorph
#print axioms TwoAxisHelicoid.harmonic_integer_induced_spin_phase
