import TwoAxisHelicoid.PositivePitchRepresentative
import TwoAxisHelicoid.EmbeddedPitchSymmetries
import TwoAxisHelicoid.OriginalAppendixBConclusions

namespace TwoAxisHelicoid
open Set Topology InnerProductSpace

/-- The parameter space supplied to compactness is the actual conformal
once-punctured complex torus of the Euclidean immersion. -/
theorem embedded_pitch_conformal_marking (W : PitchNormalizedBasicImmersion) (hW : W ∈ embeddedPitchFamily) :
    let L := rhombicPeriodPair W.t W.ht
    let Y := fun q : PuncturedPeriodTorus L => WithLp.ofLp (W.torusPosition q.1)
    ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z) := by
  obtain ⟨h,_⟩ := hW
  let L := rhombicPeriodPair W.t W.ht
  let Y := fun q : PuncturedPeriodTorus L => WithLp.ofLp (W.torusPosition q.1)
  have e : Y = harmonicTorusImmersion h := by
    funext q
    obtain ⟨z,rfl⟩ := puncturedPlaneProjection_surjective L q
    change WithLp.ofLp (W.torusPosition (periodTorusProjection L z.1)) = _
    rw [W.torusPosition_projection z.1 z.2]
    exact (harmonicTorusImmersion_projection h z.2).symm
  change ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
    ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z)
  rw [e]
  exact harmonic_quotient_pulled_regular h

/-- The local normal graphs on an original surface can be read in the
actual marked torus coordinates of its unit-pitch representative. -/
theorem embedded_pitch_position_marking (W : PitchNormalizedBasicImmersion) (hW : W ∈ embeddedPitchFamily)
    (s : OriginalHelicoidRepresentative) (hs : s.image = W.image) :
    ∃ f : PuncturedPeriodTorus (rhombicPeriodPair W.t W.ht) ≃ₜ s.carrier,
      ∀ q, s.euclideanPosition (f q) = W.torusPosition q.1 := by
  obtain ⟨h,_,_,he,_,_,_,_⟩ := embedded_pitch_family_unit_helicoid_geometry W hW
  let L := rhombicPeriodPair W.t W.ht
  let Z := fun q : PuncturedPeriodTorus L => W.torusPosition q.1
  have e : Z = coordinateToEuclidean ∘ harmonicTorusImmersion h := by
    funext q
    obtain ⟨z,rfl⟩ := puncturedPlaneProjection_surjective L q
    change W.torusPosition (periodTorusProjection L z.1) = coordinateToEuclidean (harmonicTorusImmersion h _)
    rw [W.torusPosition_projection z.1 z.2]
    exact congrArg coordinateToEuclidean (harmonicTorusImmersion_projection h z.2).symm
  have embedded := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toHomeomorph.isEmbedding
  have hZ : IsEmbedding Z := e ▸ embedded.comp he.isEmbedding
  have hS : IsEmbedding s.euclideanPosition := embedded.comp s.closedEmbedding.isEmbedding
  have hR : range Z = range s.euclideanPosition := by
    change range Z = s.image
    rw [hs,e,range_comp,harmonicTorusImmersion_range,image_image]
    rfl
  let E := Homeomorph.setCongr hR
  let f := (hZ.toHomeomorph.trans E).trans hS.toHomeomorph.symm
  exact ⟨f,fun q => congrArg Subtype.val (hS.toHomeomorph.apply_symm_apply (E (hZ.toHomeomorph q)))⟩

/-- The local normal-graph formulation of Hoffman–White, Theorem 7.1,
on sequences of actual embedded unit-pitch helicoids with their axes
marked at the origin. The limiting alternatives allow a periodic limit
and several sheets. The physical hypotheses refer to the original
Euclidean surfaces, and their charts are taken on the same images. -/
def PhysicalUnitPitchHelicoidCompactness : Prop :=
  ∀ (x : ℕ → positiveUnitPitchFamily) (s : ℕ → OriginalHelicoidRepresentative),
    (∀ n, (s n).image = (x n).1.image ∧ IsProperMap (s n).euclideanPosition ∧
      (letI : T3Space (s n).carrier := (s n).closedEmbedding.isEmbedding.t3Space
       letI := euclideanImmersionEMetricSpace (s n).euclideanPosition (s n).euclidean_smooth (s n).euclidean_immersion
       CompleteSpace (s n).carrier) ∧ (s n).axes.pitch = 1 ∧ (s n).axes.horizontalPoint = 0 ∧
      (s n).axes.horizontalDirection = 1 ∧ halfTurnX '' range (s n).position = range (s n).position ∧
      halfTurnZ '' range (s n).position = range (s n).position ∧
      (∀ (R : (Fin 3 → ℝ) ≃ₜ (Fin 3 → ℝ)) (d : ℝ), d ≠ 0 → (∀ v, R v 2 = v 2+d) →
        R '' range (s n).position ≠ range (s n).position) ∧
      (∃ f : PuncturedPeriodTorus (rhombicPeriodPair (x n).1.t (x n).1.ht) ≃ₜ (s n).carrier,
        ∀ q, (s n).euclideanPosition (f q) = (x n).1.torusPosition q.1) ∧
      let L := rhombicPeriodPair (x n).1.t (x n).1.ht
      let Y := fun q : PuncturedPeriodTorus L => WithLp.ofLp ((x n).1.torusPosition q.1)
      ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => puncturedTorusPullback L Y w j) z) ∧
        ConformalCoordinateDerivatives (puncturedTorusPullback L Y) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L Y) z)) →
    HasLocalNormalGraphLimitSubsequence x

theorem physical_unit_pitch_compactness_applies (hwv : PhysicalUnitPitchHelicoidCompactness) :
    HasLocalNormalGraphLimits positiveUnitPitchFamily := by
  intro x
  choose s hs using fun n => positive_pitch_actual_geometric_representative (x n).1 (x n).2
  apply hwv x s
  intro n
  obtain ⟨e,pitch,point,axis,period⟩ := hs n
  obtain ⟨hx,hz⟩ := pitch_geometric_half_turns _ (x n).2.1 _ e
  exact ⟨e,(s n).euclidean_proper,(s n).intrinsic_complete,pitch,point,axis,hx,hz,period,embedded_pitch_position_marking _ (x n).2.1 _ e,
    embedded_pitch_conformal_marking _ (x n).2.1⟩

/-- The original compactness argument for B.1 and B.2, with the marked
Euclidean geometric input distinguished from the verified topology,
normal cover, homology transport and flux estimates. -/
theorem original_appendix_B_by_unit_pitch_compactness (bbc : OriginalHelicoidExteriorPrinciple)
    (uniform : ∀ L, CompactGenusOneUniformization.{0} L) (hw : RhombicHelicoidIntersectionPrinciple)
    (hwv : PhysicalUnitPitchHelicoidCompactness) :
    (∃ ε : ℝ, 0 < ε ∧ (∀ W ∈ embeddedPitchFamily, ε ≤ W.t) ∧
      ∀ s : OriginalHelicoidRepresentative, ∃ W ∈ positiveUnitPitchFamily,
        ε ≤ W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  obtain ⟨⟨ε,hε,hgap⟩,hfin⟩ := local_C1_core_compactness_gives_gap_and_finite_images
    (local_normal_graph_limits_supply_core_compactness (physical_unit_pitch_compactness_applies hwv))
  constructor
  · refine ⟨ε,hε,?_,?_⟩
    · intro W hW
      obtain ⟨V,hV,ht,_⟩ := positive_pitch_representative W hW
      exact ht ▸ hgap V hV
    · intro s
      obtain ⟨W,hW,hS⟩ := original_representative_in_positive_pitch_family s bbc (uniform _) hw
      exact ⟨W,hW,hgap W hW,hS⟩
  · apply hfin.subset
    rintro _ ⟨s,rfl⟩
    obtain ⟨W,hW,hS⟩ := original_representative_in_positive_pitch_family s bbc (uniform _) hw
    exact ⟨W,hW,(Quotient.sound hS).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_appendix_B_by_unit_pitch_compactness
