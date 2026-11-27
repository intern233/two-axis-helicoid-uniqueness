import TwoAxisHelicoid.OneSidedDiskCurvature
import TwoAxisHelicoid.OriginalAnnularFluxGap

namespace TwoAxisHelicoid
open Set Topology

/-- The weak one-sided physical asymptote supplies the compact pole
model, same-marked cap, normalized map, Gauss divisor and real Morse
index from disk curvature and conformal classification of annuli. -/
theorem positional_disk_cap_normalization_and_index (schoen : PlanarSchoenfliesTheorem)
    (cm : OneSidedEmbeddedMinimalDiskEstimate) (ann : AnnularRiemannSurfaceUniformization.{0})
    (s : OriginalPositionallyAsymptoticHelicoid) :
    Nonempty (PublishedConformalPoleModel s.position) ∧ HasPointedOriginalSpinBranchCap s ∧
      HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid ∧ HasInfiniteRealSurfaceMorseIndex s.position := by
  let t := s.graphRepresentative (positional_shape_bound_of_one_sided_disks schoen cm s)
  exact ⟨(original_annular_end_pole_model_and_index t ann).1,graph_cap_normalization_and_index_from_annuli ann t⟩

/-- Theorem 1.1 on actual spatial images, including global embeddedness
of the certified immersion. The existence input has no parameter marking. -/
theorem positional_unique_class_of_one_sided_disks (schoen : PlanarSchoenfliesTheorem)
    (cm : OneSidedEmbeddedMinimalDiskEstimate) (ann : AnnularRiemannSurfaceUniformization.{0})
    (existence : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧ IsClosedEmbedding certifiedTorusImmersion :=
  positional_classification_of_pointed_models (fun s =>
    (positional_disk_cap_normalization_and_index schoen cm ann s).2.2.1) existence

/-- Appendix B on the original positional class using the same local
disk estimate, annuli and fixed-axis compactness. -/
theorem positional_disk_flux_gap_and_finiteness {I : Type*} (schoen : PlanarSchoenfliesTheorem)
    (cm : OneSidedEmbeddedMinimalDiskEstimate) (ann : AnnularRiemannSurfaceUniformization.{0})
    (family : FixedAxisHelicoidNormalClass I) (compact : family.compactCutoffs) :
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧ ∀ s : OriginalPositionallyAsymptoticHelicoid,
      ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalPositionallyAsymptoticHelicoid => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite :=
  positional_flux_gap_from_annuli_and_compactness ann (positional_shape_bound_of_one_sided_disks schoen cm) family compact

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positional_unique_class_of_one_sided_disks
#print axioms TwoAxisHelicoid.positional_disk_flux_gap_and_finiteness
