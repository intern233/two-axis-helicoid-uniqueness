import TwoAxisHelicoid.EuclideanCoreSheetCompactness
import TwoAxisHelicoid.PublishedGeometricClassification
import TwoAxisHelicoid.HorizontalLinePlacement

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The actual once-punctured surface with only positional asymptotics can
be placed in the positive unit-pitch family before using any horizontal
root bound. The meromorphic poles are taken in the published frame. -/
theorem positional_poles_give_positive_pitch_representative (s : OriginalPositionallyAsymptoticHelicoid)
    (A : PublishedConformalPoleModel s.position) (uniform : CompactGenusOneUniformization.{0} s.modelTorus)
    (hw : RhombicHelicoidIntersectionPrinciple) :
    ∃ W ∈ positiveUnitPitchFamily, (spatialSimilaritySetoid _).r s.image W.image := by
  obtain ⟨S,hs,_,L,f,Y,_,_,hf,hclosed,him,hhi,hh,hg⟩ :=
    original_smooth_surface_published_poles_to_torus s.toOriginalSmoothHelicoid uniform A s.approaches
  let _ := S
  let _ := hs
  let c := s.axes.horizontalDirection
  let P := s.axes.horizontalPoint
  let C : Fin 3 → ℝ := ![0,0,P 2]
  let R := lineAxisCoordinates c s.axes.unit C
  have hor (r : ℝ) : P+r • ![c.re,c.im,0] ∈ range (fun q : PuncturedPeriodTorus L => Y q.1) := him.symm ▸ s.axes.horizontal r
  have ver (r : ℝ) : (![0,0,r] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => Y q.1) := him.symm ▸ s.axes.vertical r
  obtain ⟨_,hE,hx,hz,reg,hh',hg'⟩ := horizontal_line_axes_placement L Y hclosed c s.axes.unit P hor ver s.axes.pitch_ne
    (him.symm ▸ s.approaches) hhi
  obtain ⟨W,hW,_,hS⟩ := marked_embedded_pitch_normalization hw L (R ∘ Y) hE hx hz reg (hh'.trans hh) (hg'.trans hg)
  let E := euclideanOrientationIsometry R (lineAxisCoordinates_dist_sq c s.axes.unit C)
  have rot : (spatialSimilaritySetoid _).r s.image (range (fun q : PuncturedPeriodTorus L => coordinateToEuclidean (R (Y q.1)))) := by
    apply image_similarity_of_surjective_parameters s.euclideanPosition _ f f.surjective 1 E 0 one_pos
    intro x
    simp only [hf,one_smul,add_zero]
    rfl
  obtain ⟨V,hV,_,hVW⟩ := positive_pitch_representative W hW
  exact ⟨V,hV,(spatialSimilaritySetoid _).trans ((spatialSimilaritySetoid _).trans rot hS) hVW⟩

/-- The compactness proof of B.1 and B.2 for the original positional
class. The global sign certificates are not used. -/
theorem positional_appendix_B_by_unit_pitch_compactness (bbc : PublishedOneHandleEndTheorem)
    (poincare : SimplyConnectedNoncompactUniformization.{0}) (hw : GeometricTwoAxisIntersectionTheorem)
    (hwv : PhysicalUnitPitchHelicoidCompactness) :
    (∃ ε : ℝ, 0 < ε ∧ (∀ W ∈ embeddedPitchFamily, ε ≤ W.t) ∧ ∀ s : OriginalPositionallyAsymptoticHelicoid,
      ∃ W ∈ positiveUnitPitchFamily, ε ≤ W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  obtain ⟨⟨ε,hε,hgap⟩,hfin⟩ := local_C1_core_compactness_gives_gap_and_finite_images
    (local_normal_graph_limits_supply_core_compactness (physical_unit_pitch_compactness_applies hwv))
  have present (s : OriginalPositionallyAsymptoticHelicoid) :
      ∃ W ∈ positiveUnitPitchFamily, (spatialSimilaritySetoid _).r s.image W.image := by
    obtain ⟨A⟩ := bbc s.toOriginalSmoothHelicoid s.intrinsic_complete s.one_topological_end s.image_ne_embedded_plane
    exact positional_poles_give_positive_pitch_representative s A (compact_genus_one_uniformization_of_classical poincare _)
      (rhombic_intersection_of_geometric_theorem hw)
  constructor
  · refine ⟨ε,hε,?_,?_⟩
    · intro W hW
      obtain ⟨V,hV,ht,_⟩ := positive_pitch_representative W hW
      exact ht ▸ hgap V hV
    · intro s
      obtain ⟨W,hW,hS⟩ := present s
      exact ⟨W,hW,hgap W hW,hS⟩
  · apply hfin.subset
    rintro _ ⟨s,rfl⟩
    obtain ⟨W,hW,hS⟩ := present s
    exact ⟨W,hW,(Quotient.sound hS).symm⟩

/-- B.1 and B.2 on the original positional class using Euclidean graph
convergence, including finite multiplicity and arbitrary periodic step. -/
theorem positional_appendix_B_from_euclidean_sheets (bbc : PublishedOneHandleEndTheorem)
    (poincare : SimplyConnectedNoncompactUniformization.{0}) (hw : GeometricTwoAxisIntersectionTheorem)
    (compactness : UnitPitchEuclideanSheetCompactness) :
    (∃ ε : ℝ, 0 < ε ∧ (∀ W ∈ embeddedPitchFamily, ε ≤ W.t) ∧ ∀ s : OriginalPositionallyAsymptoticHelicoid,
      ∃ W ∈ positiveUnitPitchFamily, ε ≤ W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite :=
  positional_appendix_B_by_unit_pitch_compactness bbc poincare hw (physical_compactness_of_euclidean_sheets compactness)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_appendix_B_by_unit_pitch_compactness
#print axioms TwoAxisHelicoid.positional_appendix_B_from_euclidean_sheets
