import TwoAxisHelicoid.SingleCutoffHandleSubsequence
import TwoAxisHelicoid.OriginalCompactCoreFluxGap

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

/-- Both generating loops are transported through a single fixed
cutoff subsequence. The velocities converge on the full parameter
intervals, so both lengths are uniformly bounded on that subsequence. -/
theorem fixed_cutoff_transports_generating_curves (η : ℝ) (eta : Real.pi/2<η)
    (compact : FixedCutoffHandleCompactness η) :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily := by
  intro x
  obtain ⟨φ,s,t,hφ,hit,cv⟩ := fixed_cutoff_normalized_handle_subsequence η eta compact x
  obtain ⟨C⟩ := exists_torus_generating_core_model s.modelTorus
  let V := {q : s.carrier | (s.topologicalType q).1∈C.carrier}
  obtain ⟨vo,_,⟨e⟩⟩ := marked_punctured_handle_core s.topologicalType C
  have chooseLoop (i : Fin 2) := original_core_loop_smooth_representative s vo ((C.loop i).map e.symm.continuous)
  choose g c cg sg val hom using chooseLoop
  obtain ⟨N,R,_,_,_,k,b,G,_,charts⟩ := original_unmarked_handles_converge_C1_on_core s C
    (fun n => (t n).toOriginalSmoothHelicoid) cv
  let W := fun n => (x (φ (n+k))).1
  let F := fun n => (t (n+k)).euclideanPosition ∘ (G n).point
  have traj (i : Fin 2) := unmarked_core_curve_velocities s b F (fun a reg => by
    obtain ⟨sc,_,dc⟩ := charts a reg
    exact ⟨fun n z hz => (sc n z hz).2,dc⟩) (g i) (cg i) (sg i)
  choose m loc using fun n => embedded_pitch_position_marking (W n) (x (φ (n+k))).2.1 (t (n+k)) (hit (n+k))
  let σ := fun n => (m n).symm ∘ (G n).point
  have pos (n : ℕ) (q : V) : (W n).torusPosition ((σ n q).1)=F n q := by
    rw [← loc]
    change (t (n+k)).euclideanPosition ((m n) ((m n).symm _))=_
    rw [(m n).apply_symm_apply]
    rfl
  choose D eq using fun n => generating_arcs_of_smooth_spatial_loops C e (W n) (x (φ (n+k))).2.1 (σ n)
    ((m n).symm.isOpenEmbedding.comp (G n).open_point) g cg c hom val (F n) (pos n) (fun i => (traj i).1 n)
  let v := fun i => deriv (s.euclideanPosition ∘ Subtype.val ∘ g i)
  refine ⟨fun n => φ (n+k),hφ.comp (strictMono_id.add_const k),D,v,
    fun i => (sg i).continuous_deriv_one.continuousOn,fun i => ?_⟩
  change TendstoUniformlyOn (fun n => deriv (coordinateToEuclidean ∘ (W n).position ∘ ((D n).arc i).curve)) (v i) atTop (Icc 0 1)
  simpa only [eq] using (traj i).2

/-- TwoAxisHelicoid Appendix B.1 and B.2 via one cutoff of the full geometric
compactness theorem. The periodic alternative is excluded by compact
handle patches. The two transported generators, the vertical flux
bound and analyticity imply a uniform gap and finitely many classes. -/
theorem original_graph_appendix_B_from_one_fixed_cutoff (η : ℝ) (eta : Real.pi/2<η)
    (compact : FixedCutoffHandleCompactness η) :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily ∧
    (∃ ε : ℝ, 0<ε ∧ (∀ W∈embeddedPitchFamily, ε≤W.t) ∧
      ∀ s : OriginalHelicoidRepresentative, ∃ W∈positiveUnitPitchFamily, ε≤W.t ∧ (spatialSimilaritySetoid _).r s.image W.image) ∧
    (range (fun s : OriginalHelicoidRepresentative => Quotient.mk (spatialSimilaritySetoid _) s.image)).Finite := by
  have loops := fixed_cutoff_transports_generating_curves η eta compact
  obtain ⟨ε,positive,gap⟩ := core_compactness_implies_uniform_parameter_gap
    (smooth_generating_curves_give_subsequential_bounded_cores loops)
  have finite := smooth_generating_core_finite_similarity_classes loops
  refine ⟨loops,⟨ε,positive,?_,?_⟩,finite.subset ?_⟩
  · intro W hW
    obtain ⟨U,hU,eq,_⟩ := positive_pitch_representative W hW
    exact eq ▸ gap U hU
  · intro s
    obtain ⟨W,hW,rel⟩ := graph_surface_has_positive_pitch_model s
    exact ⟨W,hW,gap W hW,rel⟩
  · rintro _ ⟨s,rfl⟩
    obtain ⟨W,hW,rel⟩ := graph_surface_has_positive_pitch_model s
    exact ⟨W,hW,(Quotient.sound rel).symm⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fixed_cutoff_transports_generating_curves
#print axioms TwoAxisHelicoid.original_graph_appendix_B_from_one_fixed_cutoff
