import TwoAxisHelicoid.HelicoidAxisIntersectionWinding
import TwoAxisHelicoid.HarmonicEndComparisonHelicoid
import TwoAxisHelicoid.MeromorphicSpatialOrientation

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Topology
open scoped Topology
attribute [local irreducible] thetaGauss

/-- The exact intersection statement of Hoffman and White, Theorem 2.5
(Comment. Math. Helv. 84 (2009), 551), expressed for a proper embedded
harmonic conformal parametrization of a once-punctured complex torus.
The assumption on the inverse-image helicoid expresses that it contains
the specified horizontal ruling. No integer Gauss data appear in this
statement. It is a proposition serving as a named external input. -/
def RhombicHelicoidIntersectionPrinciple : Prop :=
  ∀ {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    {α : ℝ} (hα : α ≠ 0) (b : ℝ),
    let F := harmonicTorusImmersion hX
    let A := axisSpatialNormalization hα ![0,0,b]
    let H := A ⁻¹' range (fun w : ℂ => standardHelicoid w.re w.im)
    IsClosedEmbedding F →
    (∀ x : ℝ, (![x,0,0] : Fin 3 → ℝ) ∈ range F) →
    (∀ z : ℝ, (![0,0,z] : Fin 3 → ℝ) ∈ range F) →
    HasHelicoidC1End (coordinateToTube ∘ A ∘ F) →
    H = range (axisRuledHelicoid I α 0) →
    range F ∩ H = {P | (P 1 = 0 ∧ P 2 = 0) ∨ (P 0 = 0 ∧ P 1 = 0)}

theorem harmonicTorusImmersion_range {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) :
    range (harmonicTorusImmersion hX) = X '' (L.lattice : Set ℂ)ᶜ := by
  ext P
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨z,hz⟩ := Quotient.exists_rep q.1
    have hp : periodTorusProjection L z = q.1 := hz
    have hr : z ∉ L.lattice := fun h => q.2 (hp.symm.trans ((periodTorusProjection_eq_zero L z).mpr h))
    refine ⟨z,hr,?_⟩
    rw [← harmonicTorusImmersion_projection hX hr]
    exact congrArg _ (Subtype.ext hp)
  · rintro ⟨z,hz,rfl⟩
    exact ⟨_,harmonicTorusImmersion_projection hX hz⟩

theorem harmonicTorusImmersion_closedEmbedding_of_escape {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) (hXi : Function.Injective (harmonicTorusImmersion hX))
    (he : Tendsto X (𝓝[≠] (0 : ℂ)) (cobounded (Fin 3 → ℝ)))
    (hreg : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice) :
    IsClosedEmbedding (harmonicTorusImmersion hX) := by
  have hp : IsProperMap (harmonicTorusImmersion hX) := by
    apply periodic_torus_isProperMap_of_puncture_escape L (punctureFilledMap_periodic hX.periodic)
    · intro z hz
      exact (hX.differentiable z hz).continuousAt.congr (punctureFilledMap_eventuallyEq hz).symm
    · exact he.congr' (hreg.mono (fun _ hz => (punctureFilledMap_eq hz).symm))
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap hp.continuous hXi hp.isClosedMap

/-- All the actual surface and asymptotic hypotheses in the geometric
intersection input follow from the embedded harmonic torus and its
integer Weierstrass data. Only the cited intersection principle is
passed as an external theorem. -/
theorem integer_branch_zero_or_one_of_intersection_principle
    (hHW : RhombicHelicoidIntersectionPrinciple)
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    m = 0 ∨ m = 1 := by
  obtain ⟨b,hEnd,hH⟩ := harmonic_integer_end_comparison_helicoid ht ha hc m hX hh hg
  have hD := harmonic_integer_gauss_data_has_coordinate_differential ht ha hc m hX hh hg
  have hE := harmonicTorusImmersion_closedEmbedding_of_escape hX hXi
    (integer_primitive_end_escape_and_embedding m ht ha hc hD).1 (rhombic_puncture_eventually_off_lattice ht)
  obtain ⟨hAx,hAz⟩ := harmonic_integer_data_contains_complete_axes ht ha hc m hX hh hg
  have h := hHW ht hX (integer_helicoidal_pitch_ne_zero ha hc m) b hE
    (fun x => (harmonicTorusImmersion_range hX).symm ▸ hAx x)
    (fun z => (harmonicTorusImmersion_range hX).symm ▸ hAz z) hEnd hH
  apply harmonic_integer_axis_index_of_axes_intersection ht ha hc m hX hh hg hXi
  exact ⟨b,by rwa [harmonicTorusImmersion_range hX] at h⟩

/-- For every injective actual two-axis harmonic conformal parametrization
with both original pole orders, the normalized data have index zero or one,
conditional solely on the named external intersection theorem. -/
theorem harmonic_meromorphic_index_zero_or_one_of_intersection_principle
    (hHW : RhombicHelicoidIntersectionPrinciple)
    {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hhOrder : meromorphicOrderAt
      (fun z => puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2) 0 = (-2 : ℤ))
    (hgOrder : meromorphicOrderAt (fun z =>
      deriv (fun w => nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X w)) z /
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)) 0 = (-2 : ℤ)) :
    ∃ (a c : ℝ) (m : ℤ) (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)),
      (m = 0 ∨ m = 1) ∧ a ∈ Ioo (0 : ℝ) 1 ∧ c ≠ 0 ∧ t < ellipticVerticalUpper ∧ a = verticalA t ∧
      (∀ v w : Fin 3 → ℝ, (∑ j, (R v j-R w j)^2) = ∑ j, (v j-w j)^2) ∧
      TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) (fun z => R (X z)) ∧
      (∀ z ∉ (rhombicPeriodPair t ht).lattice,
        puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun z => R (X z)) z 2 =
          coordinateData t a c ht z 2) ∧
      ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
        nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) (fun z => R (X z)) z) =
          thetaGauss t a m z := by
  obtain ⟨a,c,m,R,ha,hc,hT,ha',hR,hY,hh,hg⟩ :=
    harmonic_meromorphic_oriented_integer_data ht hX hhOrder hgOrder
  have hYi : Function.Injective (harmonicTorusImmersion hY) := by
    rw [harmonicTorusImmersion_space_map hX R hY]
    exact R.injective.comp hXi
  exact ⟨a,c,m,R,integer_branch_zero_or_one_of_intersection_principle hHW ht ha hc m hY hYi hh hg,
    ha,hc,hT,ha',hR,hY,hh,hg⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_meromorphic_index_zero_or_one_of_intersection_principle
