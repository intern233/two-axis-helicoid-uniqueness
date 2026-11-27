import TwoAxisHelicoid.FiniteSpatialSeparationCover
import TwoAxisHelicoid.CertifiedEmbeddedRepresentative
import TwoAxisHelicoid.OriginalGraphUniformizationRigidity

namespace TwoAxisHelicoid
open Set Topology

/-- Existence of an embedded representative is reduced to a finite
collection of genuine local and rational Cartesian separations on
the saturated core of the single certified immersion. Only the
implication from existence in the original class uses uniformization. -/
theorem original_graph_finite_embedding_test :
    let F := fun q j => certifiedTorusImmersion q j
    ∃ K : Set (PuncturedPeriodTorus certifiedPeriodPair), IsCompact K ∧
      immersionDoublePoints certifiedTorusImmersion ⊆ K ×ˢ K ∧
      (HasFiniteSpatialSeparationCover F K ↔ IsClosedEmbedding certifiedTorusImmersion) ∧
      (HasFiniteSpatialSeparationCover F K → Nonempty OriginalHelicoidRepresentative) ∧
      (SimplyConnectedNoncompactUniformization.{0} → (Nonempty OriginalHelicoidRepresentative ↔ HasFiniteSpatialSeparationCover F K)) := by
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let F := E ∘ certifiedTorusImmersion
  have c : Continuous F := E.continuous.comp certifiedTorusImmersion_continuous
  have loc (q : PuncturedPeriodTorus certifiedPeriodPair) : ∃ U : Set _, IsOpen U ∧ q∈U ∧ InjOn F U := by
    obtain ⟨U,ho,hq,hi⟩ := certifiedTorusImmersion_locally_injective q
    exact ⟨U,ho,hq,fun _ hx _ hy e => hi hx hy (E.injective e)⟩
  obtain ⟨_,K,k,sub,embedding⟩ := certified_compact_embedding_criterion
  have test := compact_injective_iff_finite_separation_cover (F := F) (fun j => (continuous_apply j).comp c) loc k
  have iff : HasFiniteSpatialSeparationCover F K ↔ IsClosedEmbedding certifiedTorusImmersion := by
    rw [← test,embedding]
    exact ⟨fun h _ hx _ hy eq => h hx hy (congrArg E eq),fun h _ hx _ hy eq => h hx hy (E.injective eq)⟩
  have makes (h : HasFiniteSpatialSeparationCover F K) : Nonempty OriginalHelicoidRepresentative := by
    obtain ⟨s,_⟩ := certified_original_representative_of_injective (iff.mp h).injective
    exact ⟨s⟩
  exact ⟨K,k,sub,iff,makes,fun uni => ⟨fun h => iff.mpr (certified_embedding_of_uniformization_and_original_existence uni h),makes⟩⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_graph_finite_embedding_test
