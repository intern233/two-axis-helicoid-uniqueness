import TwoAxisHelicoid.HoffmanWhiteCompactClass
import TwoAxisHelicoid.OriginalUnmarkedCoreC1
import TwoAxisHelicoid.CoordinateCurveUniformVelocities
import TwoAxisHelicoid.SpatialSmoothGeneratingArcs

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

/-- Unmarked compactness of the normalized spatial surfaces suffices
for both generating curves to have convergent velocities on a common
subsequence. The limiting surface is used in its original real
smooth structure and needs no regular torus marking. -/
theorem unmarked_cutoffs_give_smooth_generating_curves {I : Type*} (family : FixedAxisHelicoidNormalClass I)
    (compact : family.compactCutoffs) :
    HasSubsequentialSmoothGeneratingCurves positiveUnitPitchFamily := by
  intro x
  obtain ⟨φ,s,t,hφ,hit,cv⟩ := published_cutoff_original_handle_subsequence family compact x
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

/-- The flux obstruction and candidate finiteness for normalized
embedded data follow from unmarked compactness alone. -/
theorem normalized_flux_gap_and_finiteness_of_unmarked_cutoffs {I : Type*} (family : FixedAxisHelicoidNormalClass I)
    (compact : family.compactCutoffs) :
    (∃ ε : ℝ, 0<ε ∧ ∀ W∈positiveUnitPitchFamily, ε≤W.t) ∧
      ((fun W : PitchNormalizedBasicImmersion => Quotient.mk (spatialSimilaritySetoid _) W.image) '' positiveUnitPitchFamily).Finite := by
  have h := unmarked_cutoffs_give_smooth_generating_curves family compact
  exact ⟨core_compactness_implies_uniform_parameter_gap (smooth_generating_curves_give_subsequential_bounded_cores h),
    smooth_generating_core_finite_similarity_classes h⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unmarked_cutoffs_give_smooth_generating_curves
#print axioms TwoAxisHelicoid.normalized_flux_gap_and_finiteness_of_unmarked_cutoffs
