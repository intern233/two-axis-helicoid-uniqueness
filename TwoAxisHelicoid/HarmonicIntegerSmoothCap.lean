import TwoAxisHelicoid.HelicoidManifoldCap
import TwoAxisHelicoid.HeightCenteredTorusManifold
import TwoAxisHelicoid.HarmonicIntegerC1End

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold
set_option maxHeartbeats 1000000

/-- The actual embedded harmonic torus with any integer Gauss branch
admits a smooth embedded compact cap, fixing any compact parameter core.
All finite-point charts and the helicoidal end assumptions needed for
capping are derived from the actual immersion and its explicit data. -/
theorem harmonic_integer_embedded_smooth_cap
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      periodTorusLift (rhombicPeriodPair t ht) X hp q.1))
    {C : Set (PuncturedPeriodTorus (rhombicPeriodPair t ht))} (hC : IsCompact C) :
    ∃ (b : ℝ) (D : HelicoidTubeCoordinates ≃ₜ HelicoidTubeCoordinates) (R : ℝ)
      (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus (rhombicPeriodPair t ht))), let _ := cs
      let F := helicoidCompactCap (0 : PeriodTorus (rhombicPeriodPair t ht)) D R
        (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) => coordinateToTube
          (heightCenteredTorusPrimitive (rhombicPeriodPair t ht) (2*(a-m)/c) b X hp q.1))
      0 < R ∧ IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus (rhombicPeriodPair t ht)) ∧
      IsClosedEmbedding F ∧ ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) ∞ F ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,HelicoidTubeCoordinates) F q)) ∧
      ∀ q ∈ C, F q.1 = coordinateToTube
        (heightCenteredTorusPrimitive (rhombicPeriodPair t ht) (2*(a-m)/c) b X hp q.1) := by
  let L := rhombicPeriodPair t ht
  have hα : 2*(a-m)/c ≠ 0 := integer_helicoidal_pitch_ne_zero ha hc m
  obtain ⟨b,hEnd⟩ := harmonic_integer_torus_C1_helicoid_end ht ha hc m hX hp hh hg
  let Y := coordinateToTube ∘ heightCenteredTorusPrimitive L (2*(a-m)/c) b X hp
  have hproper : IsProperMap (fun q : PuncturedPeriodTorus L => Y q.1) :=
    coordinateToTube_isProperMap
      (harmonic_integer_torus_proper_and_end_injective ht ha hc m hα b hX hp hh hg).1
  have hYi : Function.Injective (fun q : PuncturedPeriodTorus L => Y q.1) := by
    dsimp only [Y]
    rw [heightCenteredTorusPrimitive_eq_space_map L hα]
    exact coordinateToTube_injective.comp
      ((axisSpatialNormalization hα ![0,0,b]).injective.comp hXi)
  refine ⟨b,?_⟩
  exact hEnd.exists_smooth_cap_from_complex_immersion (X₀ := Y)
    hproper hYi
    (fun _ hq => heightCenteredTorusPrimitive_contMDiffAt hX hp hα b hq)
    (fun _ hq => heightCenteredTorusPrimitive_mfderiv_injective hX hp hα b hq) hC

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_embedded_smooth_cap
