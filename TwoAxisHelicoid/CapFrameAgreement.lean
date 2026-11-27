import TwoAxisHelicoid.WeierstrassSpinCover

namespace TwoAxisHelicoid
open Complex Set Filter Topology

/-- Agreement on an open part of the quotient implies equality of the
actual derivatives of the lifted maps in the original complex coordinate. -/
theorem fixed_torus_cap_lift_fderiv (L : PeriodPair)
    {X : ℂ → Fin 3 → ℝ}
    (hp : ∀ z ω₀, ω₀ ∈ L.lattice → X (z+ω₀) = X z)
    {F : PeriodTorus L → Fin 3 → ℝ} {U : Set (PeriodTorus L)}
    (hU : IsOpen U) (hfix : ∀ q ∈ U, F q = periodTorusLift L X hp q)
    {z : ℂ} (hz : periodTorusProjection L z ∈ U) :
    fderiv ℝ (F ∘ periodTorusProjection L) z = fderiv ℝ X z := by
  have he : F ∘ periodTorusProjection L =ᶠ[𝓝 z] X := by
    have hpre : IsOpen (periodTorusProjection L ⁻¹' U) :=
      hU.preimage QuotientAddGroup.continuous_mk
    filter_upwards [hpre.mem_nhds hz] with w hw
    exact hfix (periodTorusProjection L w) hw
  exact he.fderiv_eq

/-- The actual normalized tangent frame of a locally fixed cap is the
already constructed Weierstrass frame, with no new frame-identification
hypothesis. This applies on any open core fixed by a smooth cap. -/
theorem harmonic_integer_cap_frame_derivative
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
    (z : PuncturedLatticePlane (rhombicPeriodPair t ht))
    (hz : periodTorusProjection (rhombicPeriodPair t ht) z.1 ∈ U) :
    (weierstrassTorusFrame ht ha m hC0 (puncturedPlaneProjection _ z)).1 =
      ((spinorWeight (weierstrassSpinorPair t a m C z.1))⁻¹ •
          fderiv ℝ (F ∘ periodTorusProjection (rhombicPeriodPair t ht)) z.1 1,
       (spinorWeight (weierstrassSpinorPair t a m C z.1))⁻¹ •
          fderiv ℝ (F ∘ periodTorusProjection (rhombicPeriodPair t ht)) z.1 I) := by
  rw [fixed_torus_cap_lift_fderiv _ hp hU hfix hz]
  exact harmonic_integer_torus_frame_derivative ht ha hc m hC0 hC hX hh hg z

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.fixed_torus_cap_lift_fderiv
#print axioms TwoAxisHelicoid.harmonic_integer_cap_frame_derivative
