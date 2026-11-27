import TwoAxisHelicoid.SignedCoreTubeCoordinate
import TwoAxisHelicoid.RegularOriginalSurfaceNormals
import TwoAxisHelicoid.TorusGeneratingCoreModels

namespace TwoAxisHelicoid
open Complex Set Metric Filter Matrix Topology
open scoped Topology ContDiff Manifold RealInnerProductSpace

/-- A single globally defined unit normal supplies Euclidean tube
coordinates about each compact subset of the original embedded torus.
The normal and transverse inverse both come from its actual immersion. -/
theorem original_smooth_compact_signed_normal_tubes (s : OriginalSmoothHelicoid) :
    ∃ N : s.carrier → SurfaceEuclideanSpace, Continuous N ∧ (∀ p, ‖N p‖=1) ∧
      ∀ K : Set s.carrier, IsCompact K → ∃ (U : Set s.carrier) (r : ℝ) (signed : SurfaceEuclideanSpace → ℝ), IsOpen U ∧ K⊆U ∧ 0<r ∧
        let W := U ×ˢ ball (0:ℝ) r
        let J := W.domRestrict (fun a : s.carrier × ℝ => s.euclideanPosition a.1+a.2 • N a.1)
        IsOpenEmbedding J ∧ ContinuousOn signed (range J) ∧ (∀ q : W, signed (J q)=q.1.2) ∧
        ∀ p∈K, ContDiffAt ℝ 1 signed (s.euclideanPosition p) ∧ signed (s.euclideanPosition p)=0 := by
  obtain ⟨N,cn,unit,_,S,data⟩ := original_smooth_regular_normal_geometry s
  let _ := S
  refine ⟨N,cn,unit,?_⟩
  intro K kc
  exact compact_regular_core_signed_tube kc
    ((surfaceCartesianEquiv.symm.injective.comp s.closedEmbedding.injective).injOn) (fun p _ => data p)

theorem original_smooth_compact_normal_tubes (s : OriginalSmoothHelicoid) :
    ∃ N : s.carrier → SurfaceEuclideanSpace, Continuous N ∧ (∀ p, ‖N p‖=1) ∧
      ∀ K : Set s.carrier, IsCompact K → ∃ (U : Set s.carrier) (r : ℝ), IsOpen U ∧ K⊆U ∧ 0<r ∧
        IsOpenEmbedding ((U ×ˢ ball (0:ℝ) r).domRestrict (fun a => s.euclideanPosition a.1+a.2 • N a.1)) := by
  obtain ⟨N,continuousN,unit,tubes⟩ := original_smooth_compact_signed_normal_tubes s
  refine ⟨N,continuousN,unit,?_⟩
  intro K hk
  obtain ⟨U,r,_,op,sub,rp,emb,_,_,_⟩ := tubes K hk
  exact ⟨U,r,op,sub,rp,emb⟩

/-- For any chosen open genus-one generating core, its actual original
image lies inside a uniform normal tube. This uses topological marking
alone to obtain a compact core disjoint from the end. -/
theorem original_generating_core_has_normal_tube (s : OriginalSmoothHelicoid) (C : TorusGeneratingCoreModel s.modelTorus) :
    ∃ (N : s.carrier → SurfaceEuclideanSpace) (U : Set s.carrier) (r : ℝ), Continuous N ∧ (∀ p, ‖N p‖=1) ∧ IsOpen U ∧
      (∀ p, (s.topologicalType p).1∈closure C.carrier → p∈U) ∧ 0<r ∧
        IsOpenEmbedding ((U ×ˢ ball (0:ℝ) r).domRestrict (fun a => s.euclideanPosition a.1+a.2 • N a.1)) := by
  let _ := periodTorus_compactSpace s.modelTorus
  let m := (Subtype.val : PuncturedPeriodTorus s.modelTorus → PeriodTorus s.modelTorus) ∘ s.topologicalType
  have en : IsEmbedding m := IsEmbedding.subtypeVal.comp s.topologicalType.isEmbedding
  have inside : closure C.carrier⊆range m := by
    intro q h
    have nq : q≠0 := fun eq => C.closure_avoids (eq ▸ h)
    exact ⟨s.topologicalType.symm ⟨q,nq⟩,congrArg Subtype.val (s.topologicalType.apply_symm_apply _)⟩
  have compact : IsCompact (m ⁻¹' closure C.carrier) := en.isCompact_iff.mpr (by rw [image_preimage_eq_of_subset inside]; exact isClosed_closure.isCompact)
  obtain ⟨N,c,u,tubes⟩ := original_smooth_compact_normal_tubes s
  obtain ⟨U,r,op,sub,pos,emb⟩ := tubes _ compact
  exact ⟨N,U,r,c,u,op,fun p hp => sub (show p∈m ⁻¹' closure C.carrier from hp),pos,emb⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.original_smooth_compact_normal_tubes
#print axioms TwoAxisHelicoid.original_generating_core_has_normal_tube
