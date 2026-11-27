import TwoAxisHelicoid.CapFrameAgreement
import TwoAxisHelicoid.SpinGeneratorHolonomy
import TwoAxisHelicoid.TorusGeneratorIntersections

namespace TwoAxisHelicoid
open Complex Set Filter Topology

theorem generator_projection_mem_fixed_core {L : PeriodPair}
    {U : Set (PeriodTorus L)}
    (hcore : Subtype.val '' puncturedGeneratorCore L ⊆ U)
    (i : Fin 2) (s : unitInterval) : periodTorusProjection L (periodBasisLine L i s) ∈ U :=
  hcore ⟨puncturedTorusGeneratorLoop L i s,puncturedTorusGeneratorLoop_mem_core L i s,rfl⟩

/-- The actual velocity of a generator on a locally fixed cap is the
velocity of the original immersion in its prescribed lattice direction. -/
theorem fixed_cap_generator_hasDerivAt {L : PeriodPair}
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X)
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → X (z+ω₀) = X z)
    {F : PeriodTorus L → Fin 3 → ℝ} {U : Set (PeriodTorus L)}
    (hU : IsOpen U) (hfix : ∀ q ∈ U, F q = periodTorusLift L X hp q)
    (hcore : Subtype.val '' puncturedGeneratorCore L ⊆ U)
    (i : Fin 2) (s : unitInterval) :
    HasDerivAt (F ∘ periodTorusProjection L ∘ periodBasisLine L i)
      (fderiv ℝ X (periodBasisLine L i s) (L.basis i)) (s : ℝ) := by
  let z := periodBasisLine L i s
  have hz : periodTorusProjection L z ∈ U := generator_projection_mem_fixed_core hcore i s
  have he : F ∘ periodTorusProjection L =ᶠ[𝓝 z] X := by
    have hpre : IsOpen (periodTorusProjection L ⁻¹' U) :=
      hU.preimage QuotientAddGroup.continuous_mk
    filter_upwards [hpre.mem_nhds hz] with w hw
    exact hfix (periodTorusProjection L w) hw
  have hd : HasFDerivAt (F ∘ periodTorusProjection L) (fderiv ℝ X z) z :=
    (hX.differentiable z (periodBasisLine_not_mem_lattice L i s)).hasFDerivAt.congr_of_eventuallyEq he
  exact hd.comp_hasDerivAt (s : ℝ) (periodBasisLine_hasDerivAt L i s)

/-- On the actual cap's two fixed generator curves, the explicit
quaternion lifts project to the cap's normalized derivative frame. -/
theorem harmonic_integer_cap_generator_frame
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : C^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    {F : PeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ}
    {U : Set (PeriodTorus (rhombicPeriodPair t ht))} (hU : IsOpen U)
    (hfix : ∀ q ∈ U, F q = periodTorusLift (rhombicPeriodPair t ht) X hp q)
    (hcore : Subtype.val '' puncturedGeneratorCore (rhombicPeriodPair t ht) ⊆ U)
    (i : Fin 2) (s : unitInterval) :
    let z := periodBasisLine (rhombicPeriodPair t ht) i s
    (unitQuaternionFrame (weierstrassGeneratorLift ht ha m hC0 i s)).1 =
      ((spinorWeight (weierstrassSpinorPair t a m C z))⁻¹ •
          fderiv ℝ (F ∘ periodTorusProjection (rhombicPeriodPair t ht)) z 1,
       (spinorWeight (weierstrassSpinorPair t a m C z))⁻¹ •
          fderiv ℝ (F ∘ periodTorusProjection (rhombicPeriodPair t ht)) z I) := by
  rw [weierstrassGeneratorLift_frame]
  exact harmonic_integer_cap_frame_derivative ht ha hc m hC0 hC hX hp hh hg hU hfix
    (puncturedBasisLine _ i s) (generator_projection_mem_fixed_core hcore i s)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.fixed_cap_generator_hasDerivAt
#print axioms TwoAxisHelicoid.harmonic_integer_cap_generator_frame
