import TwoAxisHelicoid.HarmonicIntegerTorusChart
import TwoAxisHelicoid.CertifiedC1HelicoidEnd
import TwoAxisHelicoid.PunctureFilledMap

namespace TwoAxisHelicoid
open Complex Real Set Filter Bornology Topology
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

/-- The full C¹ graph for every integer branch. Global embeddedness and
the integer selection are not hypotheses; end injectivity is derived. -/
theorem harmonic_integer_torus_C1_helicoid_end
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀ : ℂ, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    ∃ b : ℝ, HasHelicoidC1End (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      coordinateToTube (heightCenteredTorusPrimitive (rhombicPeriodPair t ht) (2*(a-m)/c) b X hp q.1)) := by
  let L := rhombicPeriodPair t ht
  let := periodTorus_compactSpace L
  let := periodTorus_t2Space L
  have hα := integer_helicoidal_pitch_ne_zero ha hc m
  obtain ⟨e,f,b,R,hf,htail,hD,hthin⟩ := harmonic_integer_torus_analytic_thin_chart ht ha hc m hX hp hh hg
  obtain ⟨hproper,C,hC,hinj⟩ := harmonic_integer_torus_proper_and_end_injective ht ha hc m hα b hX hp hh hg
  refine ⟨b,?_⟩
  apply analytic_embedded_height_end_C1_normal_graph (0 : PeriodTorus L)
    hproper hC hinj e htail 1 R hf
  · intro ξ hξ
    simpa only [Complex.ofReal_one,mul_one,Function.comp_def] using hD ξ hξ
  · exact hthin

/-- The map need only be periodic where the surface exists. Filling the
deleted lattice points with zero supplies a total representative without
changing the punctured immersion or its actual coefficient. -/
theorem harmonic_integer_data_C1_helicoid_end
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    ∃ b : ℝ, HasHelicoidC1End (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      coordinateToTube (heightCenteredTorusPrimitive (rhombicPeriodPair t ht) (2*(a-m)/c) b
        (punctureFilledMap (rhombicPeriodPair t ht) X) (punctureFilledMap_periodic hX.periodic) q.1)) := by
  apply harmonic_integer_torus_C1_helicoid_end ht ha hc m
    (hX.punctureFilled (fun _ hz => rhombic_conj_mem ht hz)) (punctureFilledMap_periodic hX.periodic)
  · intro z hz
    rw [punctureFilledMap_coefficient hz]
    exact hh z hz
  · intro z hz
    rw [punctureFilledMap_coefficient ((not_mem_gaussLogPoleSet _ _ _).mp hz).1]
    exact hg z hz

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_data_C1_helicoid_end
