import TwoAxisHelicoid.OriginalGraphUniformizationRigidity
import TwoAxisHelicoid.OriginalGraphPoleModel
import TwoAxisHelicoid.OriginalSpinBranchFromComparison
import TwoAxisHelicoid.ManuscriptSpinClassification

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- For an original C¹ representative the geometrically constructed
marked cap has even spin and the basic integer branch. Its axes
intersection, conformal end and divisor refer to the same marking. -/
theorem graph_pointed_cap_and_normalization (s : OriginalHelicoidRepresentative)
    (uni : SimplyConnectedNoncompactUniformization.{0}) :
    HasPointedOriginalSpinBranchCap s.toPositional ∧ HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
    HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid := by
  obtain ⟨A⟩ := original_graph_independent_conformal_pole_model s uni
  have cap := original_pointed_spin_cap_from_comparison s.toPositional A uni
  have norm := (pointed_spin_cap_certifies_original s.toPositional cap).2
  exact ⟨cap,norm,original_pointed_gauss_divisor_of_normalization _ norm⟩

/-- The full pointed conclusion of Theorem 1.1 for normal graph
asymptotics. Uniformization and the existence of a single genuine
embedded representative are the only literature inputs. -/
theorem theorem_1_1_for_original_c1_graphs
    (uni : SimplyConnectedNoncompactUniformization.{0}) (whw : Nonempty OriginalHelicoidRepresentative) :
    let p := certifiedClosedParameters
    let Q := spatialSimilaritySetoid (EuclideanSpace ℝ (Fin 3))
    let represents := fun c : Quotient Q => ∃ s : OriginalHelicoidRepresentative, Quotient.mk Q s.image=c
    (∃! c, represents c) ∧ represents (Quotient.mk Q (range certifiedTorusImmersion)) ∧
      IsClosedEmbedding certifiedTorusImmersion ∧
      (∀ s : OriginalHelicoidRepresentative, HasCertifiedPointedNormalization s.toOriginalSmoothHelicoid ∧
        HasOriginalPointedGaussDivisor s.toOriginalSmoothHelicoid) ∧
      certifiedPeriodPair.ω₁=2 ∧ certifiedPeriodPair.ω₂=1+I*p.t ∧
      p.t∈Ioo (866227694384/10^12:ℝ) (866227694385/10^12) ∧
      p.a∈Ioo (5936860965140/10^13:ℝ) (5936860965150/10^13) := by
  obtain ⟨s⟩ := whw
  obtain ⟨U,k,E,hk,eq⟩ := original_graph_similarity_of_classical_uniformization s uni
  have model := image_similarity_of_surjective_parameters s.euclideanPosition certifiedTorusImmersion U U.surjective k E 0 hk
    (fun x => by simpa only [add_zero] using eq x)
  refine ⟨original_graph_unique_class_of_uniformization_and_existence uni ⟨s⟩,⟨s,Quotient.sound model⟩,
    certified_embedding_of_uniformization_and_original_existence uni ⟨s⟩,fun t => (graph_pointed_cap_and_normalization t uni).2,
    rfl,rfl,?_,?_⟩
  · convert certifiedClosedParameters_bounds.1 using 1; norm_num [rootTLower,rootTUpper]
  · convert certifiedClosedParameters_bounds.2 using 1; norm_num [rootALower,rootAUpper]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.graph_pointed_cap_and_normalization
#print axioms TwoAxisHelicoid.theorem_1_1_for_original_c1_graphs
