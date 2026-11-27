import TwoAxisHelicoid.HarmonicIntegerCoordinateData
import TwoAxisHelicoid.IntegerEndProperEmbedding
import TwoAxisHelicoid.PeriodicPunctureGeometry
import TwoAxisHelicoid.AxisSpatialNormalization
import TwoAxisHelicoid.HarmonicIntegerThinEnd

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology

noncomputable def heightCenteredTorusPrimitive (L : PeriodPair) (α b : ℝ)
    (X : ℂ → Fin 3 → ℝ) (hp : ∀ z ω : ℂ, ω ∈ L.lattice → X (z+ω) = X z)
    (q : PeriodTorus L) : Fin 3 → ℝ :=
  verticalRotation I (α • (verticalRotation I (periodTorusLift L X hp q)-![0,0,b]))

@[simp] theorem heightCenteredTorusPrimitive_projection (L : PeriodPair) (α b : ℝ)
    (X : ℂ → Fin 3 → ℝ) (hp : ∀ z ω : ℂ, ω ∈ L.lattice → X (z+ω) = X z) (z : ℂ) :
    heightCenteredTorusPrimitive L α b X hp (periodTorusProjection L z) =
      heightCenteredPrimitive α b X z := rfl

theorem heightCenteredTorusPrimitive_eq_space_map (L : PeriodPair) {α : ℝ} (hα : α ≠ 0)
    (b : ℝ) (X : ℂ → Fin 3 → ℝ) (hp : ∀ z ω : ℂ, ω ∈ L.lattice → X (z+ω) = X z) :
    heightCenteredTorusPrimitive L α b X hp =
      axisSpatialNormalization hα ![0,0,b] ∘ periodTorusLift L X hp := by
  funext q
  rw [Function.comp_apply,axisSpatialNormalization_apply]
  have he : verticalRotation I (![0,0,b] : Fin 3 → ℝ) = ![0,0,b] := by
    ext j
    fin_cases j <;> simp [verticalRotation_apply]
  rw [he]
  rfl

theorem harmonic_integer_torus_proper_and_end_injective
    {t a c α : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) (hα : α ≠ 0) (b : ℝ) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω : ℂ, ω ∈ (rhombicPeriodPair t ht).lattice → X (z+ω) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    IsProperMap (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      heightCenteredTorusPrimitive (rhombicPeriodPair t ht) α b X hp q.1) ∧
      ∃ C : Set (PuncturedPeriodTorus (rhombicPeriodPair t ht)), IsCompact C ∧
        InjOn (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
          heightCenteredTorusPrimitive (rhombicPeriodPair t ht) α b X hp q.1) Cᶜ := by
  let L := rhombicPeriodPair t ht
  have hD := harmonic_integer_gauss_data_has_coordinate_differential ht ha hc m hX hh hg
  obtain ⟨hescape,K,R,_hKt,hKL,_hKR,hEmb⟩ := integer_primitive_end_escape_and_embedding m ht ha hc hD
  have hproper := periodic_torus_isProperMap_of_puncture_escape L hp
    (fun z hz => (hX.differentiable z hz).continuousAt) hescape
  obtain ⟨C,hC,hinj⟩ := periodic_torus_end_injective_of_embedded_parameter L hp
    (actualComplexHeight_tendsto (a := a) ht hc) hKL hEmb.injective
  rw [heightCenteredTorusPrimitive_eq_space_map _ hα]
  refine ⟨(axisSpatialNormalization hα ![0,0,b]).isProperMap.comp hproper,C,hC,?_⟩
  intro q hq w hw he
  exact hinj hq hw ((axisSpatialNormalization hα ![0,0,b]).injective he)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.harmonic_integer_torus_proper_and_end_injective
