import TwoAxisHelicoid.FullSpinEquivariantExtension

namespace TwoAxisHelicoid
open Complex Set Topology
set_option maxHeartbeats 1000000

variable {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)

/-- The frame angle is read from the two actual ambient vectors by real
dot products in the normalized derivative frame of the immersion. -/
noncomputable def markedImmersionSpinProjection (e : ImmersionSpatialSpin (rhombicPeriodPair t ht) X) :
    PeriodTorus (rhombicPeriodPair t ht) × Circle :=
  (e.1.1.1,frameAngle _ (spatialPlaneSpinProjection _
    ((harmonic_integer_spatial_spin_equiv ht ha hc m hC0 hC hX hh hg).symm e)))

theorem harmonic_integer_compact_spin_over_frames (s : RestrictedCompactMultiplierSpin (rhombicPeriodPair t ht)
    (latticeSpinParity (rhombicPeriodPair t ht) m)) :
    markedImmersionSpinProjection ht ha hc m hC0 hC hX hh hg
      (harmonic_integer_compact_spin_restriction ht ha hc m hC0 hC hX hh hg s) =
      compactMultiplierSpinProjection _ _ s.1 := by
  let e := harmonic_integer_compact_spin_restriction ht ha hc m hC0 hC hX hh hg s
  have he := harmonic_integer_compact_spin_square ht ha hc m hC0 hC hX hh hg s
  refine Prod.ext he.1 (Circle.ext ?_)
  change tangentPairPhase (weierstrassTorusFrame ht ha m hC0 e.1.1) (unitQuaternionFrame e.1.2) = _
  have he2 := he.2
  change unitQuaternionFrame e.1.2 = _ at he2
  rw [he2,tangentPairPhase_rotate]

/-- The ambient structure of the actual integer-branch immersion has a
unique complete cover extending any given covering identification on
the punctured frame locus. The candidate may be an arbitrary covering
space. -/
theorem harmonic_integer_induced_spin_compact_uniqueness {E : Type*} [TopologicalSpace E]
    {p : E → PeriodTorus (rhombicPeriodPair t ht) × Circle} (hp : IsCoveringMap p)
    (h : ImmersionSpatialSpin (rhombicPeriodPair t ht) X ≃ₜ {e : E // (p e).1 ≠ 0})
    (hhp : ∀ e, p (h e).1 = markedImmersionSpinProjection ht ha hc m hC0 hC hX hh hg e) :
    ∃! H : CompactMultiplierSpinBundle (rhombicPeriodPair t ht) (latticeSpinParity (rhombicPeriodPair t ht) m) ≃ₜ E,
      (∀ s, p (H s) = compactMultiplierSpinProjection _ _ s) ∧
      ∀ s : RestrictedCompactMultiplierSpin (rhombicPeriodPair t ht) (latticeSpinParity (rhombicPeriodPair t ht) m),
        H s.1 = (h (harmonic_integer_compact_spin_restriction ht ha hc m hC0 hC hX hh hg s)).1 := by
  let G := harmonic_integer_compact_spin_restriction ht ha hc m hC0 hC hX hh hg
  exact punctured_full_spin_homeomorph_extends _ _ hp (G.trans h) (fun s => (hhp (G s)).trans
    (harmonic_integer_compact_spin_over_frames ht ha hc m hC0 hC hX hh hg s))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_compact_spin_over_frames
#print axioms TwoAxisHelicoid.harmonic_integer_induced_spin_compact_uniqueness
