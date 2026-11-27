import TwoAxisHelicoid.PhysicalAnnulusFilling
import TwoAxisHelicoid.FiniteTopologyCurvatureClassification
import TwoAxisHelicoid.ManuscriptFromOneHolomorphicForm

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped Topology ContDiff Manifold

/-- An original two-axis graph end yields the actual compact marked
pole model and real Morse index using the annular classification alone.
The compact surface is constructed from the physical exterior. -/
theorem original_annular_end_pole_model_and_index (s : OriginalHelicoidRepresentative)
    (ann : AnnularRiemannSurfaceUniformization.{0}) :
    Nonempty (PublishedConformalPoleModel s.position) ∧ HasInfiniteRealSurfaceMorseIndex s.position := by
  suffices existsA : Nonempty (PublishedConformalPoleModel s.position) from
    ⟨existsA,original_real_index_of_conformal_poles s.toPositional existsA.some⟩
  obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas s.topologicalType s.smooth s.immersion s.minimal
  let _ := S
  let _ := man
  let _ := punctured_complex_curve_noncompact (0 : PeriodTorus s.modelTorus)
  have _ : NoncompactSpace s.carrier := ⟨fun h => noncompact_univ (PuncturedPeriodTorus s.modelTorus) (by
    simpa only [image_univ,s.topologicalType.surjective.range_eq] using h.image s.topologicalType.continuous)⟩
  let _ := punctured_torus_is_path_connected s.modelTorus
  let _ : ConnectedSpace s.carrier := s.topologicalType.symm.surjective.connectedSpace s.topologicalType.symm.continuous
  obtain ⟨E,_,_,G,_⟩ := original_graph_exterior_of_annular_classification s.closedEmbedding charts s.axes s.graphEnd ann
  let A : GeometricExteriorInSomeFrame s.position := ⟨LinearEquiv.refl ℝ _,fun _ _ => rfl,0,
    by simpa only [LinearEquiv.refl_apply,zero_add] using G,s.axes.pitch,s.axes.pitch_ne,
    by simpa only [LinearEquiv.refl_apply,zero_add] using s.positional.2⟩
  exact exterior_frame_constructs_compact_pole_model s.closedEmbedding.continuous charts E.connected_tails A

/-- For the weaker positional hypothesis, a scalar bound for the
original Gaussian curvature and the conformal classification of annuli
suffice to verify the actual end and the full original real Morse index.
A nonzero holomorphic differential on each compact handle then gives
the pointed cap and the unique normalized periods. -/
theorem positional_annular_cap_and_real_index (s : OriginalPositionallyAsymptoticHelicoid)
    (bound : FiniteTopologyGaussianCurvatureBound) (ann : AnnularRiemannSurfaceUniformization.{0})
    (form : GenusOneHasHolomorphicDifferential.{0}) :
    Nonempty (PublishedConformalPoleModel s.position) ∧ HasInfiniteRealSurfaceMorseIndex s.position ∧
      HasPointedOriginalSpinBranchCap s ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
      HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid := by
  obtain ⟨C,non,curv⟩ := bound s.toOriginalSmoothHelicoid
  let t := s.graphRepresentative (original_physical_shape_bound_of_gaussian _ non curv)
  obtain ⟨A,idx⟩ := original_annular_end_pole_model_and_index t ann
  have uniform := genus_one_period_uniformization_from_canonical_divisor (genus_one_canonical_divisor_of_one_section form) s.modelTorus
  have cap := original_pointed_spin_cap_of_torus_uniformization s A.some uniform
  have norm := (pointed_spin_cap_certifies_original s cap).2
  exact ⟨A,idx,cap,norm,original_pointed_gauss_divisor_of_normalization _ norm⟩

theorem positional_unique_class_of_annular_and_form (bound : FiniteTopologyGaussianCurvatureBound)
    (ann : AnnularRiemannSurfaceUniformization.{0}) (form : GenusOneHasHolomorphicDifferential.{0})
    (existence : Nonempty OriginalPositionallyAsymptoticHelicoid) :
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let rep := fun c : Quotient Q => ∃ s : OriginalPositionallyAsymptoticHelicoid, Quotient.mk Q s.image=c
    (∃! c, rep c) ∧ rep (Quotient.mk Q (range certifiedTorusImmersion)) ∧ IsClosedEmbedding certifiedTorusImmersion := by
  exact positional_classification_of_pointed_models
    (fun s => (positional_annular_cap_and_real_index s bound ann form).2.2.2.1) existence

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_annular_end_pole_model_and_index
#print axioms TwoAxisHelicoid.positional_annular_cap_and_real_index
#print axioms TwoAxisHelicoid.positional_unique_class_of_annular_and_form
